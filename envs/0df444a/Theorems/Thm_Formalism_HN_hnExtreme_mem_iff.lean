-- Prove2me | Theorems.Thm_Formalism_HN_hnExtreme_mem_iff
-- name    : Formalism.HN.hnExtreme_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:27.886807+00:00
-- url     : https://prove2.me/theorems/be566161-f388-426e-8bbb-8c5b9ff0842b
-- title:
--   HN: hn Extreme mem iff
-- statement:
--   The HN construction uses the hn Extreme mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNExtreme.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HNExtreme.lean#L21-L23

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Lemmata_GeneralBFactLeftForm_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
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
universe u v w

theorem Formalism.HN.hnExtreme_mem_iff {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by sorry
