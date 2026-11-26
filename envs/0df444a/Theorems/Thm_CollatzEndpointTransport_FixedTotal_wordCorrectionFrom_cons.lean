-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_cons
-- name    : CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:02.21992+00:00
-- url     : https://prove2.me/theorems/90570c0a-37cc-59bc-818c-747b0eed9deb
-- title:
--   Fixed Total: word Correction From cons
-- statement:
--   The Fixed Total construction uses the word Correction From cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L41-L44
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L41-L44

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_cons (i c : ℕ) (b : Bool) (bs : List Bool) :
    wordCorrectionFrom i c (b :: bs) =
      wordCorrectionFrom (i + 1)
        (if b then 3 * c + 2 ^ i else c) bs := by sorry
