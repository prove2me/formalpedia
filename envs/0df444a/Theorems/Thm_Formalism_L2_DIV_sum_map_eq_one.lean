-- Prove2me | Theorems.Thm_Formalism_L2_DIV_sum_map_eq_one
-- name    : Formalism.L2.DIV.sum_map_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:04.822264+00:00
-- url     : https://prove2.me/theorems/34bce954-cdfa-4262-b182-761e3e9d2f55
-- title:
--   DIV: sum map eq one
-- statement:
--   The DIV construction uses the sum map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L227-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L227-L230

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

theorem Formalism.L2.DIV.sum_map_eq_one (pr : Ix → Matrix (Fin n) (Fin n) K) (hsum : ∑ p, pr p = 1) (σ : K →+* ℂ) :
    ∑ p, (pr p).map σ = 1 := by sorry
