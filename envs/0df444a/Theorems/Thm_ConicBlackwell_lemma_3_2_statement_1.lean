-- Prove2me | Theorems.Thm_ConicBlackwell_lemma_3_2_statement_1
-- name    : ConicBlackwell.lemma_3_2_statement_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:34.884049+00:00
-- url     : https://prove2.me/theorems/7c5b65d1-50e4-4c51-99b1-e466e9e746d2
-- title:
--   Lemma 3.2, Statement 1 — Moreau decomposition: $u-\pi_{\mathcal C^\circ}(u)=\pi_{\mathcal C}(u)$
-- statement:
--   Let $\mathcal C\subset\mathbb R^{n+1}$ be a closed convex cone and $\mathcal C^\circ=\{z:\langle z,\hat z\rangle\le0\ \forall\hat z\in\mathcal C\}$ its polar, and write $\pi_S$ for the Euclidean projection onto $S$ (the nearest point of $S$). Then for every $u\in\mathbb R^{n+1}$:
--
--   1. $u-\pi_{\mathcal C^\circ}(u)=\pi_{\mathcal C}(u)$;
--   2. $\langle u-\pi_{\mathcal C^\circ}(u),\,\pi_{\mathcal C^\circ}(u)\rangle=0$;
--   3. $\|u-\pi_{\mathcal C^\circ}(u)\|_2\le\|u\|_2$.
--
--   This is Moreau's decomposition of a vector into its components along a cone and its polar. In the analysis of CBA$^+$ it gives the nonexpansiveness $\|\pi_{\mathcal C}(u)\|_2\le\|u\|_2$ used in the norm recursion.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: closed convex cone C ⊂ ℝⁿ⁺¹ → MoreauProx.Decomposition.IsClosedConvexCone C (nonempty, closed, convex, closed under nonnegative scaling); reason: a cone in the paper contains 0; the nonemptiness clause only excludes the empty set
--   - encoding: π_S(u), the nearest point of S to u → PerspEpi.projC S u, the unique nearest point if there is one and u otherwise; reason: on the nonempty closed convex sets C and C° the nearest point exists and is unique, so the junk value is never taken
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Lemma 3.2, Statement 1, p.7

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PerspEpi_projC
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Lemma 3.2, Statement 1** (Moreau decomposition for cones), Grand-Clément & Kroer, arXiv:2202.12277v1, p.7.
Let `C ⊂ ℝⁿ⁺¹` be a closed convex cone and `C°` its polar.  If `u ∈ ℝⁿ⁺¹`, then
`u − π_{C°}(u) = π_C(u)`, `⟨u − π_{C°}(u), π_{C°}(u)⟩ = 0`, and `‖u − π_{C°}(u)‖₂ ≤ ‖u‖₂`.

Formalization Note: `ℝⁿ⁺¹ = E (n + 1)`; "closed convex cone" is
`MoreauProx.Decomposition.IsClosedConvexCone` (nonempty, closed, convex, closed under
nonnegative scaling); `C° = polar C = {z | ∀ ẑ ∈ C, ⟪z, ẑ⟫ ≤ 0}`; `π = PerspEpi.projC`, the unique
nearest point (it exists on the nonempty closed convex sets `C` and `C°`, so the fallback value
is never used). -/
theorem lemma_3_2_statement_1 {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) (u : E (n + 1)) :
    u - PerspEpi.projC (polar C) u = PerspEpi.projC C u ∧
      ⟪u - PerspEpi.projC (polar C) u, PerspEpi.projC (polar C) u⟫ = 0 ∧
      ‖u - PerspEpi.projC (polar C) u‖ ≤ ‖u‖ := by sorry

end ConicBlackwell
