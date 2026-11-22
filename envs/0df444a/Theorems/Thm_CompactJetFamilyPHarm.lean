-- Prove2me | Theorems.Thm_CompactJetFamilyPHarm
-- name    : CompactJetFamilyPHarm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:22:10.788803+00:00
-- url     : https://prove2.me/theorems/0cf40cec-b59c-431e-b9d4-1405e1a354fc
-- title:
--   Compact Jet Family PHarm: Compact Jet Family PHarm
-- statement:
--   Every member of the compact family comes from a `p`-harmonic function.  A jet `z`
--   in `CompactJetFamily p` vanishes in its first component at the origin, has first
--   component bounded by `1`, and is the jet of a function `h` that is `p`-harmonic on
--   `ball 0 (1/2)` with weak gradient the second component of `z`.
--
--   This is the paper's assertion that every member of the family satisfies `h 0 = 0` and
--   is `p`-harmonic in `B_{1/2}`.  Note the generating set asks only for weak
--   `p`-harmonicity with an arbitrary weak gradient, while the limit passage needs the
--   CLASSICAL gradients to converge; `PHarmWeakGradClassical` is what closes that gap,
--   and without it `PHarmLimit` is unreachable from here.
--
--   The last conjunct identifies the weak gradient `G` with the CLASSICAL gradient of `h`
--   POINTWISE on the open half-ball.  It is recorded here rather than left to consumers
--   because its proof needs the approximating sequence, which is available only inside
--   this proof; a consumer holding only `z` and `h` cannot recover it.  It is what lets a
--   hypothesis about `D h 0` be read off the jet's second component at the origin.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CompactJetFamilyPHarm.lean#L24-L167
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CompactJetFamilyPHarm.lean#L24-L167

import Definitions.Def_PHigherOrder_CompactJetFamily
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Definitions.Def_PHigherOrder_PHarmLimit
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmClassicalGradient
import Definitions.Def_PHigherOrder_CompactJetFamilyPHarm
import Theorems.Thm_PHarmClassicalGradient
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_PHarmLimit
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmWeakGradClassical

set_option autoImplicit false

theorem CompactJetFamilyPHarm (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p)
    (z : BoundedContinuousFunction XHalf (ℝ × Plane))
    (hz : z ∈ CompactJetFamily p) :
    (∀ x : XHalf, (x : Plane) = 0 → (z x).1 = 0) ∧
    (∀ x : XHalf, |(z x).1| ≤ 1) ∧
    ∃ (h : Plane → ℝ) (G : Plane → Plane),
      IsPHarm p (Metric.ball 0 (1 / 2)) h G ∧
      (∀ x : XHalf, h (x : Plane) = (z x).1) ∧
      (∀ x : XHalf, G (x : Plane) = (z x).2) ∧
      Set.EqOn G (gradient h) (Metric.ball (0 : Plane) (1 / 2)) := by sorry
