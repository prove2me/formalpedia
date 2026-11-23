-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_levelsChain_of_add_one_le
-- name    : Formalism.LatticeBaseChangeAlt.levelsChain_of_add_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:34.383797+00:00
-- url     : https://prove2.me/theorems/a988d6cb-21a4-4138-ba94-b682187a5757
-- title:
--   Lattice Base Change Alt: levels Chain of add one le
-- statement:
--   The Lattice Base Change Alt construction uses the levels Chain of add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LevelsChainOfAddOneLe.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LevelsChainOfAddOneLe.lean#L9-L34

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LocalStepLevelsExt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChain
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepExtOf
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChainOfAddOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Module

theorem Formalism.LatticeBaseChangeAlt.levelsChain_of_add_one_le (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T : ℕ) (e : ℤ)
    (hep : ∀ z, 1 ≤ ep z) (hT : 1 ≤ T) (hc : 0 ≤ c') (hv : ∀ z, 0 ≤ v z)
    (hν : ∀ z, ν z ≤ νs + c' * v z) (he : (T : ℝ) * νs + 1 ≤ e) :
    ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z := by sorry
