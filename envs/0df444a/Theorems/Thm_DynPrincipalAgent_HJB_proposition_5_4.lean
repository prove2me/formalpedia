-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_proposition_5_4
-- name    : DynPrincipalAgent.HJB.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:35:02.804749+00:00
-- url     : https://prove2.me/theorems/fd7dd67b-acd6-4987-a41d-a2014da21e85
-- title:
--   Proposition 5.4, p. 30 — non-recursive representation of u_n over the quitting sequences of (5.8)
-- statement:
--   Let Assumptions 2.2 and 3.1 hold, $\theta\in\Theta$, $(t,x)\in D_\theta$ and $n\ge1$. Then $u_n(\theta;t,x)$ of (5.1) is the least upper bound of
--   $$J_n(t,x,\eta,Z,\zeta)=\mathbb E^{\zeta,Z}\Big[\int_t^{\tau_n}\big[I^h(\zeta_s;s,Z_s)-\eta_s\big]ds-\sum_{i=1}^{n-1}c^P_{\tau_i}\mathbf 1_{\{\tau_i<T\}}+\overline u_0(\tau_n)\mathbf 1_{\{\tau_n<T\}}\Big]$$
--   over $(\eta,Z,\zeta)\in\mathcal A^{\infty,\theta}_{t,x}$ (with the quitting sequence $\{\tau_i\}$ and utility $\mathcal X$ of (5.8)) subject to $\mathcal X_T=0$ on $\{\tau_n=T\}$.
--
--   The representation replaces the recursion (5.1) by a single optimization over contracts, sensitivities and hiring decisions, which is the form in which $n\to\infty$ is taken.
--
--   **Formalization Note.** The supremum is stated with `IsLUB`, which in particular makes the set nonempty and bounded above. $J_n$ is recorded only when it is a genuine expectation (integrable payoff, almost surely integrable running reward).
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Proposition 5.4, (5.9), p. 30

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Viscosity
import Definitions.Def_DynPrincipalAgent_HJB_Controls
import Definitions.Def_DynPrincipalAgent_HJB_Quitting
import Definitions.Def_DynPrincipalAgent_HJB_SelfEnforcing

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Peng1990.SMP

namespace DynPrincipalAgent.HJB

theorem proposition_5_4 {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (hM : M.Standing)
    {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ) (t : ℝ≥0) (x : ℝ)
    (hD : ((t : ℝ), x) ∈ M.D θ) (n : ℕ) (hn : 1 ≤ n) :
    IsLUB {v : ℝ | ∃ (η Z : ℝ≥0 → Ω → ℝ) (ζ : ℝ≥0 → Ω → Θ) (J : ℝ≥0 → Ω → ℝ)
        (τ : ℕ → Ω → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (I : ℝ≥0 → Ω → ℝ),
        M.InAinf S θ t x η Z ζ J τ X ∧
        (∀ᵐ ω ∂S.P, τ n ω = M.T → X M.T ω = 0) ∧
        IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha ζ Z)) I ∧
        (∀ᵐ ω ∂S.P, IntegrableOn
          (fun r : ℝ => M.Ih (ζ r.toNNReal ω) r (Z r.toNNReal ω) - η r.toNNReal ω)
          (Icc (t : ℝ) M.T)) ∧
        Integrable (fun ω =>
            (∫ r in Icc (t : ℝ) (τ n ω),
              (M.Ih (ζ r.toNNReal ω) r (Z r.toNNReal ω) - η r.toNNReal ω))
            - (∑ i ∈ Finset.Icc 1 (n - 1), if τ i ω < M.T then M.cP (τ i ω) else 0)
            + (if τ n ω < M.T then M.u0bar S (τ n ω) else 0))
          (M.girsanov S t (M.alpha ζ Z) I) ∧
        v = ∫ ω,
            ((∫ r in Icc (t : ℝ) (τ n ω),
              (M.Ih (ζ r.toNNReal ω) r (Z r.toNNReal ω) - η r.toNNReal ω))
            - (∑ i ∈ Finset.Icc 1 (n - 1), if τ i ω < M.T then M.cP (τ i ω) else 0)
            + (if τ n ω < M.T then M.u0bar S (τ n ω) else 0))
            ∂(M.girsanov S t (M.alpha ζ Z) I)}
      (M.uN S n θ t x) := by sorry

end DynPrincipalAgent.HJB
