-- Prove2me | Theorems.Thm_DedekindSubgroups_two_h_E
-- name    : DedekindSubgroups.two_h_E
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:32.491335+00:00
-- url     : https://prove2.me/theorems/7ff94564-1074-4d4a-af7b-741d678c46a2
-- title:
--   Dedekind Subgroups: two h E
-- statement:
--   `2 h E = (h² + 1) ∑ r² - k² ∑ q_r²`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L67-L80
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean#L67-L80

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.two_h_E (hk : 0 < k) (hinv : h * h' % k = 1) :
    2 * (h : ℤ) * E h k = ((h : ℤ) ^ 2 + 1) * ∑ r ∈ range k, (r : ℤ) ^ 2
      - (k : ℤ) ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 := by sorry
