-- Prove2me | Theorems.Thm_Formalism_L2_NT_eSerO_eq_zero
-- name    : Formalism.L2.NT.eSerO_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:03.91908+00:00
-- url     : https://prove2.me/theorems/f0ef3190-7c24-42cc-8607-3ac502a40224
-- title:
--   NT: e Ser O eq zero
-- statement:
--   The NT construction uses the e Ser O eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L173-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L173-L181

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

theorem Formalism.L2.NT.eSerO_eq_zero {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0)) : eSerO O r f = 0 := by sorry
