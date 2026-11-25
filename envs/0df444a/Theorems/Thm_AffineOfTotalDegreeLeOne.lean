-- Prove2me | Theorems.Thm_AffineOfTotalDegreeLeOne
-- name    : AffineOfTotalDegreeLeOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:35:11.336632+00:00
-- url     : https://prove2.me/theorems/a2de0e26-c6ca-4a0a-a5d3-5ba367d91845
-- title:
--   Affine Of Total Degree Le One: Affine Of Total Degree Le One
-- statement:
--   A polynomial of total degree at most one is an affine function: the
--   degree-`≤ 1` branch of the main theorem.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/AffineOfTotalDegreeLeOne.lean#L10-L80
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/AffineOfTotalDegreeLeOne.lean#L10-L80

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_AffineOfTotalDegreeLeOne
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem AffineOfTotalDegreeLeOne {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hdeg : P.totalDegree ≤ 1) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by sorry
