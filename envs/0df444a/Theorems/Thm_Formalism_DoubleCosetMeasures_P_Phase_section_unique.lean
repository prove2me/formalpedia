-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_section_unique
-- name    : Formalism.DoubleCosetMeasures.P.Phase.section_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:02.013186+00:00
-- url     : https://prove2.me/theorems/b93234bd-657a-4f96-ab8c-3d76715861c0
-- title:
--   Phase: section unique
-- statement:
--   The Phase construction uses the section unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L511-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L511-L541

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

theorem Formalism.DoubleCosetMeasures.P.Phase.section_unique (s : List ℕ) (t : ℕ → Kˣ) {v u h v' u' h' : Matrix (Fin s.sum) (Fin s.sum) K}
    (hh : IsLowUni h) (hh' : IsLowUni h') (hu : IsUpUni u) (hu' : IsUpUni u')
    (hvw : v * pt s t = pt s t * h) (hvw' : v' * pt s t = pt s t * h')
    (heq : v' * pt s t * u' = v * pt s t * u) : v' = v ∧ u' = u := by sorry
