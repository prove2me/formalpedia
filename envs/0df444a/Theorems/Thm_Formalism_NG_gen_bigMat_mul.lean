-- Prove2me | Theorems.Thm_Formalism_NG_gen_bigMat_mul
-- name    : Formalism.NG.gen_bigMat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:30.072563+00:00
-- url     : https://prove2.me/theorems/6b0ae94d-0e26-45ad-80a8-2301f65e14e2
-- title:
--   NG: gen big Mat mul
-- statement:
--   The NG construction uses the gen big Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L103-L108

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.gen_bigMat_mul {R O : Type*} [Ring R] [CommRing O] [Algebra O R] {m g d : Type*}
    [Fintype m] [Fintype d] [DecidableEq d] (ρ : R →ₐ[O] Matrix d d O) (C : Matrix g m R) (P : Matrix m g R) :
    bigMat (⇑ρ) (C * P) = bigRect (⇑ρ) C * bigRect (⇑ρ) P := by sorry
