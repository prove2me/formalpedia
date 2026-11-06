-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_8_c
-- name    : BinaryQueryLB.lemma_2_8_c
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:40.650194+00:00
-- url     : https://prove2.me/theorems/af1196c4-67e9-45b2-8bcf-b68c43296f55
-- title:
--   Lemma 2.8(c) — $|(x^*_W)_i|\ge 3/(4\sqrt m)$ and $W^\top x^*_W=a z^*_W$
-- statement:
--   Let $m\ge1$, $W\in\mathcal W$, $p_W$ the point of $K_W$ closest to the origin, $h_W=\|p_W\|_2$, and write $q^*_W=-p_W/h_W=(x^*_W,z^*_W)$ with $x^*_W,z^*_W\in\mathbb R^m$. Then
--   $$
--   |(x^*_W)_i|\ge\frac{3}{4\sqrt m}\quad\text{for every }i\in[m],\qquad W^\top x^*_W=\sum_i (x^*_W)_i\,w_i=a\,z^*_W .
--   $$
--
--   The identity ties the rows of $W$ to the minimizer through coefficients bounded away from zero; it is what the output-forcing argument (Lemma 3.4) exploits.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ with d ≥ 2 → any m ≥ 1; reason: every m ≥ 1 equals ⌊2m/2⌋, so the instances are the same
--   - encoding: p_W, the point of K_W closest to the origin, and h_W = ∥p_W∥₂ → every point p of K_W of least norm, with h_W = ‖p‖; reason: there is exactly one such point
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.8(c), p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_KW
import Definitions.Def_BinaryQueryLB_IsMinNormPoint
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_xPart
import Definitions.Def_BinaryQueryLB_zPart
import Definitions.Def_BinaryQueryLB_aConst

namespace BinaryQueryLB

/-- **Lemma 2.8(c) (Geometry of the minimizer).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.8(c), p.13: "Write
`q*_W = (x*_W, z*_W)` with `x*_W, z*_W ∈ R^m`. Then `|(x*_W)_i| ≥ 3/(4√m)` for every `i ∈ [m]`, and
`W⊤x*_W = a z*_W`."

Here `q*_W = −p_W/h_W`, `p_W` the point of `K_W` closest to the origin, `h_W = ∥p_W∥₂`, and
`W⊤x = Σ_i x_i w_i`.

**Formalization Note.** `m ≥ 1`; every least-norm point `p` of `K_W` is allowed. -/
theorem lemma_2_8_c (m : ℕ) (hm : 1 ≤ m) (W : Fin m → EuclideanSpace ℝ (Fin m)) (hW : W ∈ Wset m)
    (p : PtSpace m) (hp : IsMinNormPoint (KW W) p) :
    (∀ i, 3 / (4 * Real.sqrt m) ≤ |xPart (-(‖p‖⁻¹ • p)) i|) ∧
      ∑ i, xPart (-(‖p‖⁻¹ • p)) i • W i = aConst • zPart (-(‖p‖⁻¹ • p)) := by sorry

end BinaryQueryLB
