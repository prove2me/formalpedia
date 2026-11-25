-- Prove2me | Theorems.Thm_DetDLP_M3A_FpPolyDefs_coeff_spec
-- name    : DetDLP.M3A.FpPolyDefs.coeff_spec
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T21:21:54.429047+00:00
-- url     : https://prove2.me/theorems/b7cfaa13-febd-474c-aeda-bad8326f65a7
-- title:
--   Signed label coefficient evaluator
-- statement:
--   For either sign and every degree, the falling-factorial program produces the canonical residue of the generalized binomial coefficient modulo the binary precision.
-- source:
--   DetDLP, Section 4, native finite-field wire programs.

import Definitions.Def_DetDLP_M3A_FpPolyDefs

theorem DetDLP.M3A.FpPolyDefs.coeff_spec (b : Bool) (z j P : ℕ) : DetDLP.M3A.FpPolyDefs.coeff b z (2^P) j = ((DetDLP.intBinom (if b then (z:ℤ) else -(z:ℤ)) j : ℤ) : ZMod (2^P)).val := by sorry
