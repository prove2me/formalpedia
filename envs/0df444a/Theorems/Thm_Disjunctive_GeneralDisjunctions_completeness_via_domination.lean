-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_completeness_via_domination
-- name    : Disjunctive.GeneralDisjunctions.completeness_via_domination
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:01:24.020984+00:00
-- url     : https://prove2.me/theorems/427c8371-038f-4137-85f4-606a6a907b8b
-- title:
--   Theorem 11.11 — completeness and domination when Theorem 11.9 fails
-- statement:
--   This is Theorem 11.11 of Balas's *Disjunctive Programming*, the technical heart of why
--   Theorem 11.2's completeness claim holds in general, not merely under Theorem 11.9's
--   sufficient condition.
--
--   Let $\bar w:=(\bar\alpha,\bar\beta,\{\bar u^t,\bar u^t_0\}_{t\in T})$ be feasible for (11.6)
--   with every $\bar u^t_0>0$. Suppose $\bar w$ fails Theorem 11.9's sufficient condition, and no
--   positive rescaling $(\tilde\alpha,\tilde\beta)=\mu(\bar\alpha,\bar\beta)$ of it — realized by
--   some other feasible solution with those $(\alpha,\beta)$-values — satisfies it either. Then:
--
--   $$
--   \text{no intersection cut from } S \text{ is equivalent to } \bar\alpha x \ge \bar\beta.
--   $$
--
--   If in addition $(\bar\alpha,\bar\beta)$ uniquely minimizes $\alpha\bar x_N-\beta$ over (11.6),
--   then for every L\&P cut $\tilde\alpha x\ge\tilde\beta$ equivalent to an intersection cut from
--   $S$: $\bar\alpha\bar x_N-\bar\beta < \tilde\alpha\bar x_N-\tilde\beta$, and no such cut
--   dominates $\bar\alpha x\ge\bar\beta$ on $P$.
--
--   Together with Theorem 11.9, this shows the completeness picture is two-sided: when the
--   sufficient condition holds, the L\&P cut *is* an intersection cut; when it provably cannot
--   hold (even after rescaling), the L\&P cut is *not equivalent* to any intersection cut from
--   $S$, yet — under the uniqueness condition — it is *strictly better* than every intersection
--   cut from $S$ and is dominated by none of them, which is exactly what makes L\&P cuts strictly
--   more powerful than standard intersection cuts from a single $S$ in general.
--
--   **Formalization Note.** The book's own hypothesis "there is no basic feasible solution
--   $\tilde w$ to (11.6) with $(\tilde\alpha,\tilde\beta)=\mu(\bar\alpha,\bar\beta)$ ... that
--   satisfies the condition of Theorem 11.9" is formalized as `hnoscaled119`, quantifying over
--   every positive scalar $\mu$ and every feasible solution realizing that rescaled $(\alpha,
--   \beta)$-pair. `SatisfiesThm119Condition`/`IsEquivalentToIntersectionCutFromS`/`Dominates`/
--   `IsCGLP116UniqueMin` are the companion definitions built for exactly this theorem.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 164, Theorem 11.11

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp

namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.11 (Balas §11.5, p. 164-165): let `w̄:=(ᾱ,β̄,{ūᵗ,ūᵗ₀})` be a feasible solution to
(11.6) with `ūᵗ₀>0` for every `t`. If `w̄` does not satisfy Theorem 11.9's sufficient condition,
and no positive rescaling `(α̃,β̃)=μ(ᾱ,β̄)` of it (for a feasible solution with those `(α,β)`
values) satisfies it either, then there is no intersection cut from `S` equivalent to `ᾱx≥β̄`.
Furthermore, if `(ᾱ,β̄)` uniquely minimizes `αx̄_N-β` over (11.6), then `ᾱx̄_N-β̄` is strictly less
than `α̃x̄_N-β̃` for any L&P cut `α̃x≥β̃` equivalent to an intersection cut from `S`, and no such cut
dominates `ᾱx≥β̄` on `P`. -/
theorem completeness_via_domination {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (P : Set (Fin n → ℝ)) (xbarN : Fin n → ℝ)
    (alphaBar : Fin n → ℝ) (betaBar : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hfeas : IsCGLP116Feasible Atil btil d d0 alphaBar u u0 betaBar)
    (hu0pos : ∀ t, 0 < u0 t)
    (hnot119 : ¬ SatisfiesThm119Condition Atil u)
    (hnoscaled119 : ∀ μ : ℝ, 0 < μ → ∀ u' u0', 0 < μ →
      IsCGLP116Feasible Atil btil d d0 (μ • alphaBar) u' u0' (μ * betaBar) →
      ¬ SatisfiesThm119Condition Atil u') :
    ¬ IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaBar betaBar ∧
      (IsCGLP116UniqueMin Atil btil d d0 xbarN alphaBar betaBar →
        ∀ alphaT : Fin n → ℝ, ∀ betaT : ℝ,
          IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaT betaT →
          dotProduct alphaBar xbarN - betaBar < dotProduct alphaT xbarN - betaT ∧
            ¬ Dominates P alphaT betaT alphaBar betaBar) := by sorry

end Disjunctive.GeneralDisjunctions
