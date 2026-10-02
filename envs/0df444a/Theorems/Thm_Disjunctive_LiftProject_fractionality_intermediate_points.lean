-- Prove2me | Theorems.Thm_Disjunctive_LiftProject_fractionality_intermediate_points
-- name    : Disjunctive.LiftProject.fractionality_intermediate_points
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:35:38.507123+00:00
-- url     : https://prove2.me/theorems/9a1e1133-814c-4b09-a200-24915f097309
-- title:
--   Theorem 6.1 — fractionality of intermediate points
-- statement:
--   This is Theorem 6.1 of Balas's *Disjunctive Programming*: a near-substitute for the
--   (false, in general) property that sequential convexification always keeps intermediate solutions
--   integral in the variable already processed.
--
--   Let $P_1 := \mathrm{SplitConvexify}(P,1)$ and $P_{1j} := \mathrm{SplitConvexify}(P_1,j)$ for $j
--   \ge 2$. If $\alpha x \ge \beta$ is valid for $P_{1j}$ and $x^*$ is an extreme point of $P_1 \cap
--   \{\alpha x \ge \beta\}$, then
--
--   $$
--   0 < x^*_1 < 1 \implies 0 < x^*_j < 1.
--   $$
--
--   In general, an intermediate cutting plane generated while moving from $P_1$ towards $P_{1j}$ can
--   produce a fractional solution even in $x_1$ — the book's own Figures 6.1-6.2 exhibit this,
--   including with facet-defining cuts. Theorem 6.1 shows the weaker but still useful fact: *any*
--   extreme point cut off exactly at the boundary by a cut valid for the fully-convexified $P_{1j}$
--   cannot be fractional in $x_1$ without also being fractional in every other coordinate $j$ examined
--   — fractionality in one coordinate cannot be isolated.
--
--   **Formalization Note.** `SplitConvexify` is the companion definition; the theorem is stated for a
--   generic pair of coordinates `i1 ij : Fin n`, not fixed to literal indices 1 and 2.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 81, Theorem 6.1

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

namespace Disjunctive.LiftProject

/-- Theorem 6.1 (Balas §6.2, p. 81, [32]): if `αx ≥ β` is valid for `P_{1j}` and `x*` is an
extreme point of `P_1 ∩ {αx ≥ β}` with `0 < x*_1 < 1`, then `0 < x*_j < 1` too. -/
theorem fractionality_intermediate_points {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (i1 ij : Fin n) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Poly Atil btil) i1) ij, β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1) :
    0 < xstar ij ∧ xstar ij < 1 := by sorry

end Disjunctive.LiftProject
