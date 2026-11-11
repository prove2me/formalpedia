-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_display_56
-- name    : BallPolyApprox.VertexBudget.display_56
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:56:01.907467+00:00
-- url     : https://prove2.me/theorems/a2a235e9-9aeb-4fc8-ae15-24272d8518a4
-- title:
--   §5.3.3 (56) — per-simplex error $\mathbb E|1-|Y_F|^{-d}|\ge c\min\{1,|\frac1d\sum_i|v_i|^2-1|/\sqrt d\}$
-- statement:
--   There is an absolute constant $c>0$ such that, for $d\ge3$ and a $(d-1)$-simplex $F=\operatorname{conv}\{v_1,\dots,v_d\}\subset\mathbb R^d$ with $Y_F$ uniform on $F$,
--   $$\mathbb E\big|1-|Y_F|^{-d}\big|\ge c\min\Big\{1,\frac{|\frac1d\sum_i|v_i|^2-1|}{\sqrt d}\Big\}\quad(56).$$
--   In the source $F$ is a boundary simplex of a triangulation of the boundary of a polytope containing the origin in its interior; the Lean statement covers every nondegenerate $(d-1)$-simplex.
--
--   Differences from the source:
--   - generalization: F a boundary simplex of the triangulated boundary of P (o in the interior of P) → every affinely independent F = conv{v_1, …, v_d} ⊂ ℝ^d; reason: the derivation (Carbery–Wright (51), (55), Lemma 20) uses only that Y_F is uniform on a (d−1)-simplex and |Y_F| > 0 a.s.; if 0 ∈ F the expectation is +∞; boundary simplices are a special case
--   - encoding: E|1 − |Y_F|^{−d}| in ℝ → lower Lebesgue integral in [0, ∞] of |1 − (‖y‖^d)⁻¹|, compared with ENNReal.ofReal of the bound; reason: the expectation can be +∞, which a Bochner integral would turn into 0; (‖0‖^d)⁻¹ = 0 only on the null event Y_F = 0
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), §5.3.3, display (56), p. 22 (PDF 24)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- §5.3.3, display (56) (p. 22, PDF 24): there is an absolute constant `c > 0` such that for
every `d ≥ 3` and every `(d−1)`-simplex `F = conv{v_1, …, v_d} ⊂ ℝ^d` (in particular every boundary
simplex of a triangulation of the boundary of a polytope), with `Y_F` uniform on `F`,
`E|1 − |Y_F|^{−d}| ≥ c min{1, |(1/d) Σ_i |v_i|² − 1| / √d}` (the expectation may be `+∞`). -/
theorem display_56 :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 3 ≤ d → ∀ v : Fin d → Rd d, AffineIndependent ℝ v →
      ENNReal.ofReal (c * min 1 (|(1 / (d : ℝ)) * ∑ i, ‖v i‖ ^ 2 - 1| / Real.sqrt d)) ≤
        ∫⁻ y, ENNReal.ofReal |1 - (‖y‖ ^ d)⁻¹| ∂simplexUniform v := by sorry

end BallPolyApprox.VertexBudget
