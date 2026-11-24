-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_G5_adl_exists_place_ge_one
-- name    : Formalism.IndefR.Eqv.G5.adl_exists_place_ge_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:14.104803+00:00
-- url     : https://prove2.me/theorems/db5fc09f-a43c-44b8-b952-9e6321b6fa42
-- title:
--   G5: adl exists place ge one
-- statement:
--   The G5 construction uses the adl exists place ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean#L13-L32

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

theorem Formalism.IndefR.Eqv.G5.adl_exists_place_ge_one (r : 𝓞 F) (hr : r ≠ 0) :
    ∃ w : InfinitePlace F, 1 ≤ w (r : F) := by sorry
