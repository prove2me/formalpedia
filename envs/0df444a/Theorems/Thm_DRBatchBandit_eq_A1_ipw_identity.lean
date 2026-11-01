-- Prove2me | Theorems.Thm_DRBatchBandit_eq_A1_ipw_identity
-- name    : DRBatchBandit.eq_A1_ipw_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:05.551642+00:00
-- url     : https://prove2.me/theorems/64f8b2b6-901b-45aa-a1f3-c80802576d19
-- title:
--   (A.1), p.42 — inverse-propensity identity $\mathbf E_{\mathbf P_0}[f(Y(\pi(X)))]=\mathbf E_{\mathbf P_0*\pi_0}[f(Y(A))\mathbf 1\{\pi(X)=A\}/\pi_0(A\mid X)]$
-- statement:
--   Assume unconfoundedness and overlap: $\pi_0(a\mid x)\ge\eta>0$ for all $(x,a)$. Let $\pi$ be a policy and $f:\mathbb R\to\mathbb R$ a Borel measurable function. Then
--   $$\mathbf E_{\mathbf P_0}[f(Y(\pi(X)))]=\mathbf E_{\mathbf P_0*\pi_0}\Big[\frac{f(Y(\pi(X)))\mathbf 1\{\pi(X)=A\}}{\pi_0(A\mid X)}\Big]=\mathbf E_{\mathbf P_0*\pi_0}\Big[\frac{f(Y(A))\mathbf 1\{\pi(X)=A\}}{\pi_0(A\mid X)}\Big].$$
--
--   This is display (A.1) in the proof of Lemma 1. With $f(x)=e^{-x/\alpha}$ it turns the dual objective of Lemma 1 (1) into its importance-weighted form (2), and with indicator functions $f$ it identifies the means of the weighted classes of the proof of Theorem 2.
--
--   **Formalization Note** The policy is measurable. No integrability is assumed: if $f(Y(\pi(X)))$ is not integrable, neither are the weighted integrands, and Lean assigns all three expectations the value $0$, so the identity holds in that case too.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - reading: a policy π (no measurability stated) → π measurable; reason: the expectations E[Y(π(X))] presuppose a measurable π
--   - encoding: E_P with P the underlying distribution → the integral against P₀ = M.PX ⊗ₘ M.κY; reason: the proof of Lemma 1 applies (A.1) to P₀
--   - encoding: for any (Borel measurable) f (integrability left implicit) → every measurable f, no integrability hypothesis; reason: if f(Y(π(X))) is not integrable, neither weighted integrand is, and all three Bochner integrals are 0
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Lemma 1, (A.1), p.42. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_RobustValue
import Definitions.Def_DRBatchBandit_Assumptions

open MeasureTheory ProbabilityTheory

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- (A.1), proof of Lemma 1 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.42): for every
Borel measurable `f : ℝ → ℝ` and every policy `π`,
`E_{P₀}[f(Y(π(X)))] = E_{P₀∗π₀}[f(Y(π(X))) 1{π(X) = A} / π₀(A | X)]
  = E_{P₀∗π₀}[f(Y(A)) 1{π(X) = A} / π₀(A | X)]`.

**Formalization Note.** Under Assumption 1 (unconfoundedness is built into `M.law`, overlap is
`Overlap M η`). The policy is assumed measurable. No integrability is assumed: when
`f(Y(π(X)))` is not integrable, neither are the weighted integrands, and all three Bochner
integrals are `0`. -/
theorem eq_A1_ipw_identity {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) (η : ℝ)
    (hov : Overlap M η) (π : X → Fin d) (hπ : Measurable π) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ z, f (z.2 (π z.1)) ∂(P0 M) =
      ∫ ω, f (ω.2.1 (π ω.1)) * (if π ω.1 = ω.2.2 then 1 else 0) / M.e ω.1 ω.2.2 ∂M.law) ∧
    (∫ ω, f (ω.2.1 (π ω.1)) * (if π ω.1 = ω.2.2 then 1 else 0) / M.e ω.1 ω.2.2 ∂M.law =
      ∫ ω, f (ω.2.1 ω.2.2) * (if π ω.1 = ω.2.2 then 1 else 0) / M.e ω.1 ω.2.2 ∂M.law) := by sorry

end DRBatchBandit
