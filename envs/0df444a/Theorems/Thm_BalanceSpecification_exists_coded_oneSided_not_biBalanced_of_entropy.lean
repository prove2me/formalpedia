-- Prove2me | Theorems.Thm_BalanceSpecification_exists_coded_oneSided_not_biBalanced_of_entropy
-- name    : BalanceSpecification.exists_coded_oneSided_not_biBalanced_of_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:58.329381+00:00
-- url     : https://prove2.me/theorems/4fac964e-4b9e-4381-93b5-b4cfea3ed3ea
-- title:
--   Balance Specification: exists coded one Sided not bi Balanced of entropy
-- statement:
--   The complete arbitrary-positive-entropy theorem: a coded one-sided but
--   not bi-balanced shift, containing a specification subshift of the same entropy.
--   The alphabet and all shift spaces are actual finite discrete objects.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ArbitraryEntropy.lean#L29-L47
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ArbitraryEntropy.lean#L29-L47

module
public import Definitions.Def_BalanceSpecificaton_MarkerConstruction
public import Definitions.Def_BalanceSpecificaton_EntropyModel
public import Definitions.Def_BalanceSpecificaton_ArbitraryEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.exists_coded_oneSided_not_biBalanced_of_entropy {h : ℝ} (hh : 0 < h) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ X : ShiftSpace (ArbitraryEntropy.Alphabet n),
      ∃ hX : X.carrier.Nonempty,
        IsCoded X ∧ entropy X hX = h ∧
        (RightBalanced (language X) ∨ LeftBalanced (language X)) ∧
        ¬BiBalanced (language X) ∧ ¬HasVariableSpecification X ∧
        ∃ Y : ShiftSpace (ArbitraryEntropy.Alphabet n), ∃ hY : Y.carrier.Nonempty,
          Y.carrier ⊆ X.carrier ∧ HasSpecification Y ∧ entropy Y hY = h := by sorry
