-- Prove2me | Theorems.Thm_Formalism_L2_DIV_weightMet_form
-- name    : Formalism.L2.DIV.weightMet_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:48.385514+00:00
-- url     : https://prove2.me/theorems/2c2fa4d5-73ce-417f-beb6-93d27f2edffd
-- title:
--   DIV: weight Met form
-- statement:
--   The DIV construction uses the weight Met form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L217-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L217-L225

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]

theorem Formalism.L2.DIV.weightMet_form (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (weightMet pr t X v).mulVec y =
      ∑ p, ((t p v : ℝ) : ℂ) * (star (((pr p).map v.embedding).mulVec x) ⬝ᵥ
        (metOf (X v)).mulVec (((pr p).map v.embedding).mulVec y)) := by sorry
