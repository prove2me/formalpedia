-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrectionTerm_nonneg
-- name    : CollatzEndpointTransport.Terras.affineCorrectionTerm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:46.217797+00:00
-- url     : https://prove2.me/theorems/ca656ce6-f0b2-42d2-b9f7-b91aa6c5b8f9
-- title:
--   Terras: affine Correction Term nonneg
-- statement:
--   The Terras construction uses the affine Correction Term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L44-L47
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L44-L47

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.affineCorrectionTerm_nonneg (k n i : ℕ) :
    0 ≤ affineCorrectionTerm k n i := by sorry
