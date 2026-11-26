-- Prove2me | Theorems.Thm_FixedOrderFactor_castHom_natCast_eq_neg_one_iff
-- name    : FixedOrderFactor.castHom_natCast_eq_neg_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:10.236208+00:00
-- url     : https://prove2.me/theorems/1478e376-d81e-40c5-a3dc-35bad8ae09fe
-- title:
--   Fixed Order Factor: cast Hom nat Cast eq neg one iff
-- statement:
--   The Fixed Order Factor construction uses the cast Hom nat Cast eq neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L114-L117
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L114-L117

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]
omit [NeZero M]

theorem FixedOrderFactor.castHom_natCast_eq_neg_one_iff {s : ℕ} (hs : s ∣ M) (x : ℕ) :
    ZMod.castHom hs (ZMod s) (x : ZMod M) = -1 ↔ s ∣ x + 1 := by sorry
