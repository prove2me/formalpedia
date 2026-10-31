-- Prove2me | Theorems.Thm_AubinLipschitz_clarke_surjective_contingent_approx
-- name    : AubinLipschitz.clarke_surjective_contingent_approx
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:17.657997+00:00
-- url     : https://prove2.me/theorems/d95b606e-f82c-452b-9d9d-916d1388b105
-- title:
--   §3, Lemma 1, pp.27–28 — approximate surjectivity of nearby contingent derivatives, as the proof gives it
-- statement:
--   Let $X,Y$ be finite-dimensional, $F$ a set-valued map from $X$ to $Y$, and $(x_0,y_0)\in\operatorname{graph}(F)$. Assume that the Clarke derivative $CF(x_0,y_0)$ maps $X$ onto $Y$. Then for all $\alpha>0$ there are $c>0$, $\eta>0$ such that for all $(x,y)\in\operatorname{graph}(F)$ with $\|x-x_0\|+\|y-y_0\|\le\eta$ and all $v\in Y$ there exist $u\in X$, $w\in Y$ with
--
--   $$
--   v\in DF(x,y)(u)+w,\qquad \|u\|\le c\|v\|,\qquad \|w\|\le\alpha\|v\|.
--   $$
--
--   This is the conclusion the proof of the Lemma reaches at p.28, and it is exactly hypothesis (6) of Theorem 2 of §3. The Lemma's printed form, without $w$ in the inclusion, is the separate item `contingent_surjective_of_clarke_surjective`.
--
--   Differences from the source:
--   - reading: printed (16) is "v ∈ DF(x,y)(u), ‖u‖ ≤ c‖v‖ and ‖w‖ ≤ α‖v‖", with w unused → Lean has v ∈ DF(x,y)(u) + w; reason: the proof constructs v₀ ∈ DF(x,y)(u₀ − u_α) + v_α and sets w = (‖v‖/γ) v_α (p.28), and Theorem 2 (6)i needs exactly this form. The printed form, which implies this one with w = 0, is the companion item contingent_surjective_of_clarke_surjective.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Lemma 1 and its proof, pp.27–28

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_contingentDeriv
import Definitions.Def_AubinLipschitz_IsSurjectiveProcess

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Lemma 1, p.27, in the form its proof establishes (pp.27–28): if `CF(x₀, y₀)`
maps `X` onto `Y`, then for all `α > 0` there are `c > 0`, `η > 0` such that for all
`(x, y) ∈ graph(F)` with `‖x − x₀‖ + ‖y − y₀‖ ≤ η` and all `v ∈ Y` there are `u ∈ X`, `w ∈ Y`
with `v ∈ DF(x, y)(u) + w`, `‖u‖ ≤ c‖v‖` and `‖w‖ ≤ α‖v‖`. -/
theorem clarke_surjective_contingent_approx {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : X → Set Y) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀)
    (hsurj : IsSurjectiveProcess (clarkeDeriv F x₀ y₀)) (α : ℝ) (hα : 0 < α) :
    ∃ c > 0, ∃ η > 0, ∀ (x : X) (y : Y), y ∈ F x → ‖x - x₀‖ + ‖y - y₀‖ ≤ η → ∀ v : Y,
      ∃ (u : X) (w : Y), (∃ z ∈ contingentDeriv F x y u, v = z + w) ∧
        ‖u‖ ≤ c * ‖v‖ ∧ ‖w‖ ≤ α * ‖v‖ := by sorry

end AubinLipschitz
