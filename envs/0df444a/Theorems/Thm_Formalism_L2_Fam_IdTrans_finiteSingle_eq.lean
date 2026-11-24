-- Prove2me | Theorems.Thm_Formalism_L2_Fam_IdTrans_finiteSingle_eq
-- name    : Formalism.L2.Fam.IdTrans.finiteSingle_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:04.891742+00:00
-- url     : https://prove2.me/theorems/d176ff6a-28d6-4aae-873c-d7f911b1f8ec
-- title:
--   Id Trans: finite Single eq
-- statement:
--   The Id Trans construction uses the finite Single eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NumberFieldFamilies/IdTransSM.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NumberFieldFamilies/IdTransSM.lean#L95-L108

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
open Classical

theorem Formalism.L2.Fam.IdTrans.finiteSingle_eq (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) (hx : x ∈ v.adicCompletionIntegers L) :
    finiteSingle L v x = RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite
      (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L)) := by sorry
