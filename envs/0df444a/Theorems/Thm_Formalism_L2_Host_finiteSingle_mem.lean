-- Prove2me | Theorems.Thm_Formalism_L2_Host_finiteSingle_mem
-- name    : Formalism.L2.Host.finiteSingle_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:39.184468+00:00
-- url     : https://prove2.me/theorems/e5052968-446f-4f05-84ed-3a12f2b5be94
-- title:
--   Host: finite Single mem
-- statement:
--   The Host construction uses the finite Single mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L41-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/UnrAEPf.lean#L41-L78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.L2.Host.finiteSingle_mem (Vf : Set (FiniteAdeleRing (𝓞 L) L)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 L) L)) :
    ∃ S : Set (HeightOneSpectrum (𝓞 L)), S.Finite ∧ ∀ v, v ∉ S → ∀ y : v.adicCompletion L,
      y ∈ v.adicCompletionIntegers L → finiteSingle L v y ∈ Vf := by sorry
