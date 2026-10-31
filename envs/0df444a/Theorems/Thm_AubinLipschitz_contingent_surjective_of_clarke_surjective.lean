-- Prove2me | Theorems.Thm_AubinLipschitz_contingent_surjective_of_clarke_surjective
-- name    : AubinLipschitz.contingent_surjective_of_clarke_surjective
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:17.984158+00:00
-- url     : https://prove2.me/theorems/afac8228-cfcd-4f5b-84c2-f8094dc2e3bb
-- title:
--   §3, Lemma 1, (16), as printed — nearby contingent derivatives are uniformly surjective
-- statement:
--   Let $X,Y$ be finite-dimensional, $F$ a set-valued map from $X$ to $Y$, and $(x_0,y_0)\in\operatorname{graph}(F)$. Assume that the Clarke derivative $CF(x_0,y_0)$ maps $X$ onto $Y$. Then for all $\alpha>0$ there are $c>0$, $\eta>0$ such that for all $(x,y)\in\operatorname{graph}(F)$ with $\|x-x_0\|+\|y-y_0\|\le\eta$ and all $v\in Y$ there exist $u\in X$, $w\in Y$ with
--
--   $$
--   v\in DF(x,y)(u),\qquad\|u\|\le c\|v\|,\qquad\|w\|\le\alpha\|v\|.
--   $$
--
--   This is the Lemma with (16) exactly as printed; $w$ plays no part in the inclusion. The printed proof gives only the form with $v\in DF(x,y)(u)+w$ (item `clarke_surjective_contingent_approx`), but the printed form does follow from the Inverse Function Theorem applied to the closure of the graph (which has the same contingent cones at points of the graph and a larger Clarke cone) and compactness.
--
--   Differences from the source: none.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Lemma 1, (15)–(16), p.27

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_contingentDeriv
import Definitions.Def_AubinLipschitz_IsSurjectiveProcess

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Lemma 1, (16), p.27, as printed: if `CF(x₀, y₀)` maps `X`
onto `Y`, then for all `α > 0` there are `c > 0`, `η > 0` such that for all `(x, y) ∈ graph(F)`
with `‖x − x₀‖ + ‖y − y₀‖ ≤ η` and all `v ∈ Y` there are `u ∈ X`, `w ∈ Y` with `v ∈ DF(x, y)(u)`,
`‖u‖ ≤ c‖v‖` and `‖w‖ ≤ α‖v‖`.

**Formalization Note** `F` is an arbitrary set-valued map, as in the Lemma; `w` plays no part in
the inclusion, as printed. -/
theorem contingent_surjective_of_clarke_surjective {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : X → Set Y) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀)
    (hsurj : IsSurjectiveProcess (clarkeDeriv F x₀ y₀)) (α : ℝ) (hα : 0 < α) :
    ∃ c > 0, ∃ η > 0, ∀ (x : X) (y : Y), y ∈ F x → ‖x - x₀‖ + ‖y - y₀‖ ≤ η → ∀ v : Y,
      ∃ (u : X) (w : Y), v ∈ contingentDeriv F x y u ∧ ‖u‖ ≤ c * ‖v‖ ∧ ‖w‖ ≤ α * ‖v‖ := by sorry

end AubinLipschitz
