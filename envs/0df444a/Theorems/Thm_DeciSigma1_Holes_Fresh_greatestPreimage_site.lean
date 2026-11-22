-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_site
-- name    : DeciSigma1.Holes.Fresh.greatestPreimage_site
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:35.334799+00:00
-- url     : https://prove2.me/theorems/c43ee957-05c5-40c6-a464-b127278335bb
-- title:
--   Fresh: greatest Preimage site
-- statement:
--   At a junction the greatest preimage is the right end of the site.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L112-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L112-L120

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.greatestPreimage_site (hs : StrictlySeparated δ cs) {c : ℕ} (hc : c ∈ cs) :
    greatestPreimage (sitePositions δ cs) (retainedCount (sitePositions δ cs) c) = c + δ := by sorry
