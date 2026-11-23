-- Prove2me | Theorems.Thm_Formalism_L2_DIV_map_surj
-- name    : Formalism.L2.DIV.map_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:14.762206+00:00
-- url     : https://prove2.me/theorems/d08d2e94-da29-4c1e-9ace-3aebd2679db8
-- title:
--   DIV: map surj
-- statement:
--   The DIV construction uses the map surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L45-L49

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

theorem Formalism.L2.DIV.map_surj {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (P : Matrix (Fin d) (Fin n) K)
    (h : Function.Surjective P.mulVec) : Function.Surjective (P.map σ).mulVec := by sorry
