-- Prove2me | Theorems.Thm_EpAlgHomogeneous
-- name    : EpAlgHomogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:31:42.139294+00:00
-- url     : https://prove2.me/theorems/c02df10d-1156-4b82-9d73-9415beb596a8
-- title:
--   Ep Alg Homogeneous: Ep Alg Homogeneous
-- statement:
--   If `P` is homogeneous of degree `m ≥ 2` then `EpAlg p P` is homogeneous of
--   degree `3*m - 4`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpAlgHomogeneous.lean#L10-L39
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpAlgHomogeneous.lean#L10-L39

module
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_EpAlgHomogeneous
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem EpAlgHomogeneous {n : ℕ} (p : ℝ) {m : ℕ} (hm : 2 ≤ m)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m) :
    (EpAlg p P).IsHomogeneous (3 * m - 4) := by sorry
