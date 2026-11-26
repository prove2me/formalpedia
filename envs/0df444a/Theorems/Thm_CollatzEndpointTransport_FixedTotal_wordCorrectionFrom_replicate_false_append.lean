-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_replicate_false_append
-- name    : CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_replicate_false_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:29.490297+00:00
-- url     : https://prove2.me/theorems/cce8d214-5416-42f3-abbf-d143e8deeaa2
-- title:
--   Fixed Total: word Correction From replicate false append
-- statement:
--   The Fixed Total construction uses the word Correction From replicate false append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L58-L68
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L58-L68

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_replicate_false_append
    (i c r : ℕ) (ys : List Bool) :
    wordCorrectionFrom i c (List.replicate r false ++ ys) =
      wordCorrectionFrom (i + r) c ys := by sorry
