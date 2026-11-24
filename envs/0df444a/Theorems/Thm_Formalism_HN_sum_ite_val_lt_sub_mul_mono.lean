-- Prove2me | Theorems.Thm_Formalism_HN_sum_ite_val_lt_sub_mul_mono
-- name    : Formalism.HN.sum_ite_val_lt_sub_mul_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:45.382851+00:00
-- url     : https://prove2.me/theorems/cbeb96aa-58ab-4ffc-aab7-575e9dbe3ca3
-- title:
--   HN: sum ite val lt sub mul mono
-- statement:
--   The HN construction uses the sum ite val lt sub mul mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNSlopes.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNSlopes.lean#L46-L58

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.sum_ite_val_lt_sub_mul_mono (n m₁ m₂ : ℕ) (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (x : Fin n → ℝ) (a : ℝ)
    (hx : ∀ j : Fin n, m₁ ≤ (j : ℕ) → (j : ℕ) < m₂ → a ≤ x j) :
    (∑ j : Fin n, if (j : ℕ) < m₁ then x j else 0) - a * m₁ ≤
      (∑ j : Fin n, if (j : ℕ) < m₂ then x j else 0) - a * m₂ := by sorry
