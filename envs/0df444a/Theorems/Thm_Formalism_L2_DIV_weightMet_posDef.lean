-- Prove2me | Theorems.Thm_Formalism_L2_DIV_weightMet_posDef
-- name    : Formalism.L2.DIV.weightMet_posDef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:42.906897+00:00
-- url     : https://prove2.me/theorems/4d6acf6c-98d5-41d4-a1d8-9c01c1db0c06
-- title:
--   DIV: weight Met pos Def
-- statement:
--   The DIV construction uses the weight Met pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L232-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L232-L257

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

theorem Formalism.L2.DIV.weightMet_posDef (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (ht : ∀ p v, 0 < t p v) (hsum : ∑ p, pr p = 1) (v : InfinitePlace K) :
    (weightMet pr t X v).PosDef := by sorry
