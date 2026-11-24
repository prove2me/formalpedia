-- Prove2me | Theorems.Thm_Formalism_L2_NT_hasLabelO_spec
-- name    : Formalism.L2.NT.hasLabelO_spec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:08:49.635752+00:00
-- url     : https://prove2.me/theorems/8ba71c7c-918c-4db4-8520-3f1304d2b17f
-- title:
--   NT: has Label O spec
-- statement:
--   The NT construction uses the has Label O spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L147-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L147-L171

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.PT
variable {g : ℕ} [Fact g.Prime]

theorem Formalism.L2.NT.hasLabelO_spec {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) {r : ℕ}
    {τ : FDRep ℂ (GL (Fin r) (ZMod g))} {f : (ZMod g)[X]} (h : HasLabelO O τ f) :
    f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0 := by sorry
