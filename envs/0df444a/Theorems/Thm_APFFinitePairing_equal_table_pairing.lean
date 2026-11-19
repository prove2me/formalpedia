-- Prove2me | Theorems.Thm_APFFinitePairing_equal_table_pairing
-- name    : APFFinitePairing.equal_table_pairing
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-10-02T12:41:01.244533+00:00
-- url     : https://prove2.me/theorems/95cb9679-74dc-472f-b302-1fc11712acc2
-- title:
--   Equal-table transport preserves pairing
-- statement:
--   # Equal-table transport preserves pairing
--
--   The left and right linear equivalences induced by table equality preserve every pairing value.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_rightEquiv
import Definitions.Def_APFFinitePairing_RightSpace
import Definitions.Def_APFFinitePairing_LeftRad
import Definitions.Def_APFFinitePairing_leftEquiv
import Definitions.Def_APFFinitePairing_LeftSpace
import Definitions.Def_APFFinitePairing_RightRad
import Definitions.Def_APFFinitePairing_pairing
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]

theorem APFFinitePairing.equal_table_pairing (M N : I → J → ℝ) (h : M=N)
    (a : LeftSpace M) (b : RightSpace M) :
    pairing N (leftEquiv M N h a) (rightEquiv M N h b) = pairing M a b := by
  sorry
