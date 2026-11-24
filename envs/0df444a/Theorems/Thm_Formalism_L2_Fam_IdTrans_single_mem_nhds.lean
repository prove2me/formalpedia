-- Prove2me | Theorems.Thm_Formalism_L2_Fam_IdTrans_single_mem_nhds
-- name    : Formalism.L2.Fam.IdTrans.single_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:55.313481+00:00
-- url     : https://prove2.me/theorems/9478f378-1421-472b-9346-7d40da9b1c87
-- title:
--   Id Trans: single mem nhds
-- statement:
--   The Id Trans construction uses the single mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NumberFieldFamilies/IdTransSM.lean#L110-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NumberFieldFamilies/IdTransSM.lean#L110-L136

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
open Formalism Formalism.L2 Formalism.L2.Fam Formalism.L2.Fam.IdTrans
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.L2.Fam.IdTrans.single_mem_nhds {S : Set (AdeleRing (𝓞 L) L)} (hS : S ∈ 𝓝 (1 : AdeleRing (𝓞 L) L)) :
    ∃ I : Set (HeightOneSpectrum (𝓞 L)), I.Finite ∧ ∀ v ∉ I, ∀ (x : v.adicCompletion L) (_hx : x ∈ v.adicCompletionIntegers L),
      (((1 : InfiniteAdeleRing L), finiteSingle L v x) : AdeleRing (𝓞 L) L) ∈ S := by sorry
