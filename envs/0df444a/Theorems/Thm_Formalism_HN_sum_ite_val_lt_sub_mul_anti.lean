-- Prove2me | Theorems.Thm_Formalism_HN_sum_ite_val_lt_sub_mul_anti
-- name    : Formalism.HN.sum_ite_val_lt_sub_mul_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:38.988615+00:00
-- url     : https://prove2.me/theorems/1701de2a-68ea-4da2-86f5-85fbac30fe81
-- title:
--   HN: sum ite val lt sub mul anti
-- statement:
--   The HN construction uses the sum ite val lt sub mul anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNSlopes.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNSlopes.lean#L60-L72

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

theorem Formalism.HN.sum_ite_val_lt_sub_mul_anti (n m₁ m₂ : ℕ) (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (x : Fin n → ℝ) (a : ℝ)
    (hx : ∀ j : Fin n, m₁ ≤ (j : ℕ) → (j : ℕ) < m₂ → x j ≤ a) :
    (∑ j : Fin n, if (j : ℕ) < m₂ then x j else 0) - a * m₂ ≤
      (∑ j : Fin n, if (j : ℕ) < m₁ then x j else 0) - a * m₁ := by sorry
