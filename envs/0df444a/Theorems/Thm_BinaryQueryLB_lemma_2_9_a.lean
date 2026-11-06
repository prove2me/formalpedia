-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_9_a
-- name    : BinaryQueryLB.lemma_2_9_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:47:54.03786+00:00
-- url     : https://prove2.me/theorems/4c95d18d-c81f-4fce-adb8-99e7e08fd359
-- title:
--   Lemma 2.9(a) — $\Phi_W(q)-f_W(q^\circ)=(r(q)-1)(f_W(q^\circ)+b)\ge0$
-- statement:
--   Let $m\ge1$ and $W\in\mathcal W$. For $q\in\mathbb R^{2m}$ write $r(q)=\max\{1,\|q\|_2\}$ and $q^\circ=q/r(q)$. Then
--   $$
--   \Phi_W(q)-f_W(q^\circ)=(r(q)-1)\big(f_W(q^\circ)+b\big)\ge0 .
--   $$
--
--   So projecting a point radially onto the unit ball never increases the objective.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ with d ≥ 2 → any m ≥ 1; reason: every m ≥ 1 equals ⌊2m/2⌋, so the instances are the same
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.9(a), p.14

import Mathlib
import Definitions.Def_BinaryQueryLB_PhiW
import Definitions.Def_BinaryQueryLB_radialProj
import Definitions.Def_BinaryQueryLB_Wset

namespace BinaryQueryLB

/-- **Lemma 2.9(a) (Box and ball).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.9(a), p.14: "For `q ∈ R^{2m}` write
`r(q) = max{1, ∥q∥₂}` and `q° = q/r(q)`. For every `W ∈ 𝒲`: (a)
`Φ_W(q) − f_W(q°) = (r(q) − 1)(f_W(q°) + b) ≥ 0`".

**Formalization Note.** `m ≥ 1`; `q°` is `radialProj q`. Both the identity and the inequality are
stated. -/
theorem lemma_2_9_a (m : ℕ) (hm : 1 ≤ m) (W : Fin m → EuclideanSpace ℝ (Fin m)) (hW : W ∈ Wset m) (q : PtSpace m) :
    PhiW W q - fW W (radialProj q) = (max 1 ‖q‖ - 1) * (fW W (radialProj q) + bConst m) ∧
      0 ≤ (max 1 ‖q‖ - 1) * (fW W (radialProj q) + bConst m) := by sorry

end BinaryQueryLB
