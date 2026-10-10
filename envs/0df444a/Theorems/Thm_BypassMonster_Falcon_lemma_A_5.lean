-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_5
-- name    : BypassMonster.Falcon.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:39.475011+00:00
-- url     : https://prove2.me/theorems/73948f93-64f6-4fef-ad99-4a635af5d4e2
-- title:
--   Lemma A.5, p. 1924 — Σ_π Qₘ(π) Reĝ(π) ≤ K/γₘ
-- statement:
--   Consider Setup 2. For every epoch $m\ge1$ and every outcome of the run, the randomized policy $Q_m$ has small predicted implicit regret:
--   $$\sum_{\pi\in\Psi}Q_m(\pi)\,\widehat{\mathrm{Reg}}_m(\pi)\le\frac{K}{\gamma_m},$$
--   where $\widehat{\mathrm{Reg}}_m(\pi)=\hat{\mathcal R}_m(\pi_{\hat f_m})-\hat{\mathcal R}_m(\pi)$ is the regret of $\pi$ measured by the predictor $\hat f_m$.
--
--   Together with Lemma A.6 this is the "exploration–exploitation" property of the inverse-gap-weighted kernel: low predicted regret, controlled divergence.
--
--   **Formalization Note** $\widehat{\mathrm{Reg}}_t$ for a round $t$ of epoch $m$ is indexed by $m$. `Setup2` supplies $\gamma_m>0$ (through $\mathcal E>0$ and the strictly increasing schedule) and the tie-breaking rule's maximality. Finite $\mathcal X$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.5 and its proof, p. 1924

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.5** (p. 1924): for every epoch `m ≥ 1` and outcome `ω`,
`∑_{π ∈ Ψ} Q_m(π) Reĝ(π) ≤ K/γ_m`, where `Reĝ` is the predicted implicit regret of epoch `m`. -/
theorem lemma_A_5
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) (m : ℕ) (hm : 1 ≤ m) (ω : Params.Omega X K) :
    ∑ π : X → Fin K, A.Qm m ω π * A.RegHat DX m ω π ≤ (K : ℝ) / A.gamma m := by sorry

end BypassMonster.Falcon
