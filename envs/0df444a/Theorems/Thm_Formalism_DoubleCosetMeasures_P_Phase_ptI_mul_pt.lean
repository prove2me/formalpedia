-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_ptI_mul_pt
-- name    : Formalism.DoubleCosetMeasures.P.Phase.ptI_mul_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:51.686728+00:00
-- url     : https://prove2.me/theorems/08be5172-79ce-4461-b2f0-ddcbe8faa4cf
-- title:
--   Phase: pt I mul pt
-- statement:
--   The Phase construction uses the pt I mul pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L156-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L156-L163

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

theorem Formalism.DoubleCosetMeasures.P.Phase.ptI_mul_pt (s : List ℕ) (t : ℕ → Kˣ) : ptI s t * pt s t = (1 : Matrix _ _ K) := by sorry
