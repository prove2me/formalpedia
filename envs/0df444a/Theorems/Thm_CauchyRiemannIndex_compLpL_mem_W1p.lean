-- Prove2me | Theorems.Thm_CauchyRiemannIndex_compLpL_mem_W1p
-- name    : CauchyRiemannIndex.compLpL_mem_W1p
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T16:07:04.395988+00:00
-- url     : https://prove2.me/theorems/b9b8aded-5838-4ebe-9218-1da22b801ef4
-- title:
--   Pointwise linear maps preserve W^{1,p} on the cylinder
-- statement:
--   Let $1\le p\le\infty$, $a,b\ge0$, and let $L:\mathbb{R}^{2a}\to\mathbb{R}^{2b}$ be linear. If $(u,v,w)\in L^p\times L^p\times L^p$ lies in $W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2a})$ (in its realisation as the closure of the triples $(u,\partial_s u,\partial_t u)$ of test sections), then the pointwise image $(L u, L v, L w)$ lies in $W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2b})$.
--
--   This lets one move Sobolev triples between trivial bundles of different ranks, for example along the coordinate projections and inclusions of a direct-sum splitting $\mathbb{R}^{2(a+b)}=\mathbb{R}^{2a}\oplus\mathbb{R}^{2b}$.
--
--   **Formalization Note** `W1p p n` is the setting module's closed span of the test triples in `Triple n p`; the pointwise image of `f : LpCyl a p` under `L` is Mathlib's `L.compLpL p cylMeasure f`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, §4.1 (Sobolev spaces on the cylinder)

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- Applying a fixed linear map `L : ℝ^{2a} → ℝ^{2b}` pointwise to each component of a triple
`(u, ∂ₛu, ∂ₜu)` in `W^{1,p}(ℝ × S¹, ℝ^{2a})` gives a triple in `W^{1,p}(ℝ × S¹, ℝ^{2b})`. -/
theorem compLpL_mem_W1p {a b : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (L : Vec a →L[ℝ] Vec b)
    {w : Triple a p} (hw : w ∈ W1p p a) :
    (L.compLpL p cylMeasure w.1, L.compLpL p cylMeasure w.2.1, L.compLpL p cylMeasure w.2.2) ∈
      W1p p b := by
  sorry

end CauchyRiemannIndex
