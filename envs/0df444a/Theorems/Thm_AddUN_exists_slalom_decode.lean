-- Prove2me | Theorems.Thm_AddUN_exists_slalom_decode
-- name    : AddUN.exists_slalom_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:25:04.643632+00:00
-- url     : https://prove2.me/theorems/d08969c9-f69b-4ea4-84ef-f5c556358364
-- title:
--   Add UN: exists slalom decode
-- statement:
--   The coding lemma for the map `decode` and the width `2 ^ (3 * mu n + n)`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L342-L406
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L342-L406

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open Coding

theorem AddUN.exists_slalom_decode {K : Set (ℕ → Bool)} (hK : IsCompact K) (hKpos : cantorMeasure K ≠ 0)
    (c : ℕ → Bool) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ 2 ^ (3 * mu n + n)) ∧
      ∀ f : ℕ → ℕ, (∃ᶠ n in atTop, f n ∉ S n) → ∃ w ∈ K, decode f w = c := by sorry
