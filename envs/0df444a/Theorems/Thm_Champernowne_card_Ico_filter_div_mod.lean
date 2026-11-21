-- Prove2me | Theorems.Thm_Champernowne_card_Ico_filter_div_mod
-- name    : Champernowne.card_Ico_filter_div_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:27.751949+00:00
-- url     : https://prove2.me/theorems/7012cd96-8e5f-4182-98f4-c6a5bc1b4a45
-- title:
--   Champernowne: card Ico filter div mod
-- statement:
--   Exact periodic counting: over an interval whose endpoints are multiples
--   of `p * q`, the value `n / p % q` hits a fixed `d < q` exactly `p` times
--   per period `p * q`. Only the lower bound `le_card_Ico_filter_div_mod`
--   (proved directly in `DigitCount.lean`) feeds `champernowne_normal`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L204-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L204-L271

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_Ico_filter_div_mod {A B p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) (hB : p * q ∣ B) :
    ((Finset.Ico A B).filter (fun n => n / p % q = d)).card
      = (B / (p * q) - A / (p * q)) * p := by sorry
