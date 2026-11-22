-- Prove2me | Theorems.Thm_Formalism_L2_DIV_majAt_eq
-- name    : Formalism.L2.DIV.majAt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:50.742574+00:00
-- url     : https://prove2.me/theorems/7c80d6f9-011e-41f5-9e65-fe567ed1bb4a
-- title:
--   DIV: maj At eq
-- statement:
--   The DIV construction uses the maj At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L59-L68

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

theorem Formalism.L2.DIV.majAt_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec (fun i => v.embedding (y i)) := by sorry
