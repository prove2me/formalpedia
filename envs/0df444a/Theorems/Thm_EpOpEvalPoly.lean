-- Prove2me | Theorems.Thm_EpOpEvalPoly
-- name    : EpOpEvalPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:39.964036+00:00
-- url     : https://prove2.me/theorems/4658812b-f0c8-4d3f-a97c-e13fea54b516
-- title:
--   Ep Op Eval Poly: Ep Op Eval Poly
-- statement:
--   The single bridge between the analytic operator `EpOp` and its algebraic
--   avatar `EpAlg`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpOpEvalPoly.lean#L12-L41
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpOpEvalPoly.lean#L12-L41

module
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_EpOp
public import Definitions.Def_PHarmonicPoly_MvPolyLaplacian
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Theorems.Thm_MvPolyLaplacian

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem EpOpEvalPoly {n : ℕ} (p : ℝ) (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = MvPolynomial.eval (fun i => x i) (EpAlg p P) := by sorry
