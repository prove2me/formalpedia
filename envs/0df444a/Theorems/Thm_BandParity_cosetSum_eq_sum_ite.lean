-- Prove2me | Theorems.Thm_BandParity_cosetSum_eq_sum_ite
-- name    : BandParity.cosetSum_eq_sum_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:47.717969+00:00
-- url     : https://prove2.me/theorems/1775e154-fed6-4cea-9c51-3b78a415b639
-- title:
--   Band Parity: coset Sum eq sum ite
-- statement:
--   The Band Parity construction uses the coset Sum eq sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L42-L44
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L42-L44

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.cosetSum_eq_sum_ite (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) :
    cosetSum χ z = ∑ n : ZMod p, if χ n = z then (n.val : ℤ) else 0 := by sorry
