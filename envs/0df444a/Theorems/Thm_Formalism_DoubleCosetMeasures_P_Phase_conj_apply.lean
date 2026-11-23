-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_conj_apply
-- name    : Formalism.DoubleCosetMeasures.P.Phase.conj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:43.23668+00:00
-- url     : https://prove2.me/theorems/88006155-c7a3-494d-8a40-8d74551bc39a
-- title:
--   Phase: conj apply
-- statement:
--   The Phase construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L165-L169

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

theorem Formalism.DoubleCosetMeasures.P.Phase.conj_apply (s : List ℕ) (t : ℕ → Kˣ) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (ptI s t * M * pt s t) a c =
      (((t (blk s a))⁻¹ : Kˣ) : K) * M (revF s a) (revF s c) * ((t (blk s c) : Kˣ) : K) := by sorry
