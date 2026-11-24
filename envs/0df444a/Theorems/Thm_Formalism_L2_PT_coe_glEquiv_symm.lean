-- Prove2me | Theorems.Thm_Formalism_L2_PT_coe_glEquiv_symm
-- name    : Formalism.L2.PT.coe_glEquiv_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:53.163836+00:00
-- url     : https://prove2.me/theorems/c5157c73-cebc-426a-8652-6842ebc2cc13
-- title:
--   PT: coe gl Equiv symm
-- statement:
--   The PT construction uses the coe gl Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L61-L62

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

theorem Formalism.L2.PT.coe_glEquiv_symm (e : ι ≃ κ) (γ : GL κ K) :
    (((glEquiv K e).symm γ : GL ι K) : Matrix ι ι K) = Matrix.reindex e.symm e.symm (γ : Matrix κ κ K) := by sorry
