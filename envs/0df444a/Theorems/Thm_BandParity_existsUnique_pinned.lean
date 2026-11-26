-- Prove2me | Theorems.Thm_BandParity_existsUnique_pinned
-- name    : BandParity.existsUnique_pinned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:12:25.531058+00:00
-- url     : https://prove2.me/theorems/c26b2abd-398b-489e-87b2-961abb6a90d2
-- title:
--   Band Parity: exists Unique pinned
-- statement:
--   **The pin.** For `p ≡ 5 (mod 8)` there is a unique quartic character with `χ 2 = i`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L44-L46
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L44-L46

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.existsUnique_pinned (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := by sorry
