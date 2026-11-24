-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_G5_adl_inf_cocompact
-- name    : Formalism.IndefR.Eqv.G5.adl_inf_cocompact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:02.008302+00:00
-- url     : https://prove2.me/theorems/99934c49-0201-4397-9f62-dbbd1e640c1f
-- title:
--   G5: adl inf cocompact
-- statement:
--   The G5 construction uses the adl inf cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean#L96-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/AdlEqZeroOfMemNbhd.lean#L96-L136

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

theorem Formalism.IndefR.Eqv.G5.adl_inf_cocompact : ∃ C : Set (InfiniteAdeleRing F), IsCompact C ∧
    ∀ y, ∃ r : 𝓞 F, y - algebraMap F _ (r : F) ∈ C := by sorry
