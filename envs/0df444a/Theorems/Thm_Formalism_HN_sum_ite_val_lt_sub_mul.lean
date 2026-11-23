-- Prove2me | Theorems.Thm_Formalism_HN_sum_ite_val_lt_sub_mul
-- name    : Formalism.HN.sum_ite_val_lt_sub_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:56.204335+00:00
-- url     : https://prove2.me/theorems/a7fce2dd-18c8-4db3-8728-8cc249188ff7
-- title:
--   HN: sum ite val lt sub mul
-- statement:
--   The HN construction uses the sum ite val lt sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNSlopes.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNSlopes.lean#L36-L44

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

theorem Formalism.HN.sum_ite_val_lt_sub_mul (n m : ℕ) (hm : m ≤ n) (x : Fin n → ℝ) (a : ℝ) :
    (∑ j : Fin n, if (j : ℕ) < m then x j else 0) - a * m =
      ∑ j : Fin n, if (j : ℕ) < m then x j - a else 0 := by sorry
