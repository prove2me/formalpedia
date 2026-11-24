-- Prove2me | Theorems.Thm_Formalism_L2_PT_character_transp
-- name    : Formalism.L2.PT.character_transp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:43.060805+00:00
-- url     : https://prove2.me/theorems/7b170db2-9cfb-42a4-b84a-7c9d85671a5d
-- title:
--   PT: character transp
-- statement:
--   The PT construction uses the character transp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L67-L68

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

theorem Formalism.L2.PT.character_transp (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (γ : GL κ K) :
    (transp e τ).character γ = τ.character ((glEquiv K e).symm γ) := by sorry
