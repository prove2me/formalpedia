-- Prove2me | Theorems.Thm_DataDrivenRO_KS_support_lagrangian
-- name    : DataDrivenRO.KS.support_lagrangian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:10.066636+00:00
-- url     : https://prove2.me/theorems/b52a7500-45b4-485e-823a-c1855acd6df8
-- title:
--   Proof of Theorem 5, p. ec4 — Lagrangian duality: δ*(v|𝒰^I_ε) = inf_{λ>0} {λ log(1/ε) + max_{q,θ} [Σᵢ vᵢ Σⱼ û^(j)_i qⁱⱼ − λ Σᵢ D(qⁱ, θᵢq^L + (1−θᵢ)q^R)]}
-- statement:
--   In the setting of §5.1 (with $N\ge1$, $0<\Gamma<1$ and $0<\epsilon<1$), fix $v\in\mathbb R^d$. For $\lambda>0$ let
--   $$L(\lambda)=\sup\Big\{\sum_{i=1}^dv_i\sum_{j=0}^{N+1}\hat u^{(j)}_iq^i_j-\lambda\sum_{i=1}^dD\big(q^i,\theta_iq^L+(1-\theta_i)q^R\big)\ :\ q^i\in\Delta_{N+2},\ 0\le\theta_i\le1\Big\},$$
--   the supremum running over the choices for which every divergence is finite. Then:
--
--   1. for every $\lambda>0$ the set over which the supremum is taken is nonempty and bounded above, so $L(\lambda)$ is a genuine supremum;
--   2. the support function of $\mathcal U^I_\epsilon$ is
--   $$\delta^*(v\mid\mathcal U^I_\epsilon)=\inf_{\lambda>0}\big\{\lambda\log(1/\epsilon)+L(\lambda)\big\}.$$
--
--   This is the Lagrangian dual of the convex program $\max\{v^{\mathsf T}u:u\in\mathcal U^I_\epsilon\}$ obtained by dualizing the divergence budget; the inner problem then decouples across coordinates.
--
--   **Formalization Note** The support function is the published `RobustMDP.Shared.supportFunction`, $\delta^*(v\mid\mathcal U)=\sup_{u\in\mathcal U}\sum_ju_jv_j$. The infimum is taken over $\lambda>0$ and stated as `IsGLB`; the page's $\inf_{\lambda\ge0}$ has the same value. The "max" of the page is written as a supremum (`sSup`) whose nonemptiness and boundedness are part of the conclusion.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 5, display after "By Lagrangian duality", p. ec4

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem support_lagrangian {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    let inner : ℝ → Set ℝ := fun lam =>
      {s | ∃ (θ : Fin d → ℝ) (q : Fin d → Fin (N + 2) → ℝ),
        (∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ i, q i ∈ stdSimplex ℝ (Fin (N + 2))) ∧
        (∀ i, AbsCont (q i) (mix N Γ (θ i))) ∧
        s = ∑ i, v i * ∑ j, uhat i j * q i j - lam * ∑ i, relEntropy (q i) (mix N Γ (θ i))}
    (∀ lam, 0 < lam → (inner lam).Nonempty ∧ BddAbove (inner lam)) ∧
    IsGLB ((fun lam => lam * Real.log (1 / ε) + sSup (inner lam)) '' Set.Ioi 0)
      (RobustMDP.Shared.supportFunction (UI uhat Γ ε) v) := by sorry

end DataDrivenRO.KS
