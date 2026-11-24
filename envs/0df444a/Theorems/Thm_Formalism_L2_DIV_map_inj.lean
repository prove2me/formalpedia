-- Prove2me | Theorems.Thm_Formalism_L2_DIV_map_inj
-- name    : Formalism.L2.DIV.map_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:24.987683+00:00
-- url     : https://prove2.me/theorems/dccded13-2d52-45cc-8f20-af39e9e38f23
-- title:
--   DIV: map inj
-- statement:
--   The DIV construction uses the map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L39-L43

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

theorem Formalism.L2.DIV.map_inj {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (h : Function.Injective E.mulVec) : Function.Injective (E.map σ).mulVec := by sorry
