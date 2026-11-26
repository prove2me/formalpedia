-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_append
-- name    : CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:38.44079+00:00
-- url     : https://prove2.me/theorems/7587c34e-a7a2-4e1d-bc4f-e2ccdb0ee504
-- title:
--   Fixed Total: word Correction From append
-- statement:
--   The Fixed Total construction uses the word Correction From append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L46-L56
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L46-L56

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_append
    (i c : ℕ) (xs ys : List Bool) :
    wordCorrectionFrom i c (xs ++ ys) =
      wordCorrectionFrom (i + xs.length)
        (wordCorrectionFrom i c xs) ys := by sorry
