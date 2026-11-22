-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_codim_inf_le
-- name    : Formalism.CountingSumsFrames.codim_inf_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:58.676338+00:00
-- url     : https://prove2.me/theorems/5669ad07-5b32-4f93-8d6e-5013f37010ce
-- title:
--   Counting Sums Frames: codim inf le
-- statement:
--   The Counting Sums Frames construction uses the codim inf le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L187-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L187-L208

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.CountingSumsFrames.codim_inf_le [DecidableEq ι] (Y : Submodule K V) [FiniteDimensional K Y] (A : ι → Submodule K V) :
    ∀ s : Finset ι, Module.finrank K Y - Module.finrank K (Y ⊓ s.inf A : Submodule K V) ≤
      ∑ i ∈ s, (Module.finrank K Y - Module.finrank K (Y ⊓ A i : Submodule K V)) := by sorry
