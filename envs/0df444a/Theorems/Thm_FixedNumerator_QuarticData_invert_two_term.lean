-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_invert_two_term
-- name    : FixedNumerator.QuarticData.invert_two_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:34.965804+00:00
-- url     : https://prove2.me/theorems/4315bc53-8140-5eef-9dde-6fe1053600c2
-- title:
--   Quartic Data: invert two term
-- statement:
--   Inverting `S(Y) = T(Y) + a T(Y / M)`: `T(X) = ∑_{j ≤ X} (-a)^j S(X / M^j)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L126-L152
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L126-L152

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)

theorem FixedNumerator.QuarticData.invert_two_term (S T : ℕ → ℂ) (a : ℂ) {M : ℕ} (hM : 2 ≤ M) (hT0 : T 0 = 0)
    (h : ∀ Y, S Y = T Y + a * T (Y / M)) :
    ∀ X n, X + 1 ≤ n → T X = ∑ j ∈ range n, (-a) ^ j * S (X / M ^ j) := by sorry
