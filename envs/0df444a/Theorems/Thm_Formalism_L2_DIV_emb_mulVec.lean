-- Prove2me | Theorems.Thm_Formalism_L2_DIV_emb_mulVec
-- name    : Formalism.L2.DIV.emb_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:48.91681+00:00
-- url     : https://prove2.me/theorems/f4cbfcf8-3509-4352-83f9-5005e7c9f2ff
-- title:
--   DIV: emb mul Vec
-- statement:
--   The DIV construction uses the emb mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L70-L73

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

theorem Formalism.L2.DIV.emb_mulVec {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (x : Fin d → K) : (fun i => σ (E.mulVec x i)) = (E.map σ).mulVec (fun a => σ (x a)) := by sorry
