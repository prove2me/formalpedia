-- Prove2me | Theorems.Thm_DedekindSubgroups_even_inv_sq
-- name    : DedekindSubgroups.even_inv_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:05:47.782906+00:00
-- url     : https://prove2.me/theorems/7666d7d5-353d-5808-bf48-ce3e58149d52
-- title:
--   Dedekind Subgroups: even inv sq
-- statement:
--   Inversions of a square are even: `σ_{g²} = σ_g ∘ σ_g`, and the sign is multiplicative.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L111-L123
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L111-L123

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.even_inv_sq {g g' : ℕ} (hk : 0 < k) (hinv : g * g' % k = 1) :
    Even (inv (g * g % k) k) := by sorry
