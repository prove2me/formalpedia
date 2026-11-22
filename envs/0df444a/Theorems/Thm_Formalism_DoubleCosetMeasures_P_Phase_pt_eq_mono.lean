-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_eq_mono
-- name    : Formalism.DoubleCosetMeasures.P.Phase.pt_eq_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:16.617465+00:00
-- url     : https://prove2.me/theorems/7a955631-4507-47c7-993c-7a341b773965
-- title:
--   Phase: pt eq mono
-- statement:
--   The Phase construction uses the pt eq mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L135-L142

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]

theorem Formalism.DoubleCosetMeasures.P.Phase.pt_eq_mono (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t = mono s (fun a => ((t (blk s a) : Kˣ) : K)) := by sorry
