-- Prove2me | Theorems.Thm_Formalism_L2_DIV_normAt_eq
-- name    : Formalism.L2.DIV.normAt_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:48.380565+00:00
-- url     : https://prove2.me/theorems/2296437e-678c-4968-8aa8-d8cb684054a0
-- title:
--   DIV: norm At eq
-- statement:
--   The DIV construction uses the norm At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L303-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L303-L311

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

theorem Formalism.L2.DIV.normAt_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x =
      Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by sorry
