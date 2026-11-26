-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_castSucc
-- name    : CollatzEndpointTransport.FixedTotal.parityVec_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:28.471956+00:00
-- url     : https://prove2.me/theorems/5fbc100a-cc86-45e2-bff2-6d3d289dd70c
-- title:
--   Fixed Total: parity Vec cast Succ
-- statement:
--   The Fixed Total construction uses the parity Vec cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L152-L156
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L152-L156

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.parityVec_castSucc
    (M n : ℕ) :
    (fun i : Fin M => Terras.parityVec (M + 1) n i.castSucc) =
      Terras.parityVec M n := by sorry
