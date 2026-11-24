-- Prove2me | Theorems.Thm_Formalism_HN_shiftInv_sum
-- name    : Formalism.HN.shiftInv_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:35.299393+00:00
-- url     : https://prove2.me/theorems/83eaf5e8-6bab-4233-83f0-f24877a9c55b
-- title:
--   HN: shift Inv sum
-- statement:
--   The HN construction uses the shift Inv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L100-L109

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
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
universe u v w w₂

theorem Formalism.HN.shiftInv_sum {n m : ℕ} (h : m = n) (f : Fin n → ℝ) (g : Fin m → ℝ) (c : ℝ) (k : ℕ)
    (hfg : ∀ (j : ℕ) (h1 : j < m) (h2 : j < n), g ⟨j, h1⟩ = f ⟨j, h2⟩ + c) :
    (∑ j : Fin m, if (j : ℕ) < k then g j else 0) =
      (∑ j : Fin n, if (j : ℕ) < k then f j else 0) + c * ((min k n : ℕ) : ℝ) := by sorry
