-- Prove2me | Theorems.Thm_Formalism_L2_mem_mapPl
-- name    : Formalism.L2.mem_mapPl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:39.14111+00:00
-- url     : https://prove2.me/theorems/62c1b37b-fb95-4163-ad60-da725acf7139
-- title:
--   L2: mem map Pl
-- statement:
--   The L2 construction uses the mem map Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PlaceMapInjectivity/MapPlInjective.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PlaceMapInjectivity/MapPlInjective.lean#L17-L20

import Definitions.Def_Formalism_ConjugateSelfDual_StatementRest
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PlaceMapInjectivity_MapPlInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open Formalism Formalism.L2

theorem Formalism.L2.mem_mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    RingOfIntegers.mapRingEquiv j x ∈ (mapPl j v).asIdeal ↔ x ∈ v.asIdeal := by sorry
