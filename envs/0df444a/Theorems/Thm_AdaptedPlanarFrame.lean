-- Prove2me | Theorems.Thm_AdaptedPlanarFrame
-- name    : AdaptedPlanarFrame
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:26:37.648801+00:00
-- url     : https://prove2.me/theorems/af82f583-3387-4424-8ea9-bc0f294c1fd9
-- title:
--   Adapted Planar Frame: Adapted Planar Frame
-- statement:
--   An orthonormal basis of `EuclideanSpace ℝ (Fin n)` adapted to the plane
--   spanned by an orthonormal pair `e, v`: two of its vectors are the rotated planar
--   frame `cos θ • e + sin θ • v` and `-sin θ • e + cos θ • v`, and every other basis
--   vector is orthogonal to both `e` and `v`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/AdaptedPlanarFrame.lean#L11-L145
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/AdaptedPlanarFrame.lean#L11-L145

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
set_option autoImplicit false
@[expose] public section
public section

theorem AdaptedPlanarFrame {n : ℕ} (hn : 2 ≤ n) {e v : EuclideanSpace ℝ (Fin n)}
    (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hev : inner ℝ e v = (0 : ℝ)) (th : ℝ) :
    ∃ (i0 i1 : Fin n) (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
      i0 ≠ i1
        ∧ b i0 = (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))
        ∧ b i1 = ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n))
        ∧ ∀ i : Fin n, i ≠ i0 → i ≠ i1 →
            (inner ℝ e (b i) : ℝ) = 0 ∧ (inner ℝ v (b i) : ℝ) = 0 := by sorry
