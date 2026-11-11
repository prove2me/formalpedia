-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_12
-- name    : BallPolyApprox.VertexBudget.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:55:18.813333+00:00
-- url     : https://prove2.me/theorems/f4d53108-7d2d-4435-b765-c6f61c5471d4
-- title:
--   Lemma 12 — three formulas for the interpolation gap $W_T$
-- statement:
--   Let $m\ge1$, $k=m+1$ and $T=\operatorname{conv}\{v_1,\dots,v_k\}\subset\mathbb R^m$ a nondegenerate simplex with barycentric coordinates $\lambda_i(x)$. For every $x\in T$,
--   $$W_T(x)=\sum_{1\le i<j\le k}\lambda_i(x)\lambda_j(x)|v_i-v_j|^2=\sum_{i=1}^k\lambda_i(x)|x-v_i|^2=R_T^2-|x-z_T|^2\quad(27),$$
--   where $z_T$ and $R_T$ are the circumcenter and circumradius of $T$.
--
--   Differences from the source:
--   - encoding: nondegenerate simplex T = conv{v_1, …, v_k} → affinely independent v : Fin (m+1) → ℝ^m, x ∈ convexHull (range v), circumcenter/circumradius of the Mathlib Affine.Simplex with these points; reason: Mathlib's notion of a nondegenerate simplex; indices run over Fin (m+1)
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 12, p. 14 (PDF 16)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 12 (p. 14, PDF 16): for a nondegenerate simplex `T = conv{v_1, …, v_k} ⊂ ℝ^m`
(`k = m + 1`, `m ≥ 1`) with barycentric coordinates `λ_i(x)`, every `x ∈ T` satisfies
`W_T(x) = Σ_{i<j} λ_i λ_j |v_i − v_j|² = Σ_i λ_i |x − v_i|² = R_T² − |x − z_T|²` (27), where
`z_T`, `R_T` are the circumcenter and circumradius of `T`. -/
theorem lemma_12 (m : ℕ) (hm : 1 ≤ m) (v : Fin (m + 1) → Rd m) (hv : AffineIndependent ℝ v)
    (x : Rd m) (hx : x ∈ convexHull ℝ (Set.range v)) :
    interpGap v x =
        ∑ i, ∑ j ∈ Finset.Ioi i, baryCoord v x i * baryCoord v x j * ‖v i - v j‖ ^ 2 ∧
      interpGap v x = ∑ i, baryCoord v x i * ‖x - v i‖ ^ 2 ∧
      interpGap v x =
        (⟨v, hv⟩ : Affine.Simplex ℝ (Rd m) m).circumradius ^ 2 -
          ‖x - (⟨v, hv⟩ : Affine.Simplex ℝ (Rd m) m).circumcenter‖ ^ 2 := by sorry

end BallPolyApprox.VertexBudget
