-- Prove2me | Theorems.Thm_EpAlgSmul
-- name    : EpAlgSmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:58:42.559683+00:00
-- url     : https://prove2.me/theorems/5dcb2abd-6a74-4900-a6ff-99582d8a7a61
-- title:
--   Ep Alg Smul: Ep Alg Smul
-- statement:
--   `E_p` is cubic in its argument: `EpAlg p (c • P) = c^3 • EpAlg p P`. This is
--   what licenses the paper's normalization (replacing `u` by `-u` and scaling).
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpAlgSmul.lean#L10-L35
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/EpAlgSmul.lean#L10-L35

module
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_EpAlgSmul
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem EpAlgSmul {n : ℕ} (p c : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    EpAlg p (c • P) = c ^ 3 • EpAlg p P := by sorry
