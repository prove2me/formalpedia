-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_G5_adl_eq_zero_of_mem_nbhd
-- name    : Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:09.462817+00:00
-- url     : https://prove2.me/theorems/4df936d5-a2ef-560d-9b5a-cdd7cf785a3f
-- title:
--   G5: adl eq zero of mem nbhd
-- statement:
--   The G5 construction uses the adl eq zero of mem nbhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean#L74-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean#L74-L94

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing

theorem Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (a : F) (ha : algebraMap F (AdeleRing (𝓞 F) F) a ∈ adlNbhd F) : a = 0 := by sorry
