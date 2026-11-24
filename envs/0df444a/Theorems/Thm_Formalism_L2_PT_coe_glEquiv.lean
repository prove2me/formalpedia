-- Prove2me | Theorems.Thm_Formalism_L2_PT_coe_glEquiv
-- name    : Formalism.L2.PT.coe_glEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:19.239258+00:00
-- url     : https://prove2.me/theorems/ddd1f8ee-ab0e-4a42-8378-3c1b0f479261
-- title:
--   PT: coe gl Equiv
-- statement:
--   The PT construction uses the coe gl Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L58-L59

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
open Formalism Formalism.L2 Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem Formalism.L2.PT.coe_glEquiv (e : ι ≃ κ) (u : GL ι K) :
    ((glEquiv K e u : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (u : Matrix ι ι K) := by sorry
