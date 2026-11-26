-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_concat
-- name    : CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:56.672317+00:00
-- url     : https://prove2.me/theorems/583482b7-8298-5007-a977-591461b6d40b
-- title:
--   Fixed Total: word Correction From concat
-- statement:
--   The Fixed Total construction uses the word Correction From concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L142-L150
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L142-L150

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_concat
    (i c : ℕ) (xs : List Bool) (b : Bool) :
    wordCorrectionFrom i c (xs.concat b) =
      if b then
        3 * wordCorrectionFrom i c xs + 2 ^ (i + xs.length)
      else
        wordCorrectionFrom i c xs := by sorry
