-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_le_v_sum
-- name    : Formalism.L2.FormalSeriesBounds.S4.le_v_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:42.184158+00:00
-- url     : https://prove2.me/theorems/8521e19a-613d-42d8-ad52-25181e34359b
-- title:
--   S4: le v sum
-- statement:
--   The S4 construction uses the le v sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L20-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.S4.le_v_sum (v : AddValuation R (WithTop ℝ)) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → R) (g : WithTop ℝ) (hg : ∀ i ∈ s, g ≤ v (f i)) : g ≤ v (∑ i ∈ s, f i) := by sorry
