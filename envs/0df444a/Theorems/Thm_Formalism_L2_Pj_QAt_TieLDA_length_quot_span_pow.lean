-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_length_quot_span_pow
-- name    : Formalism.L2.Pj.QAt.TieLDA.length_quot_span_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:33.404872+00:00
-- url     : https://prove2.me/theorems/c3917fc0-49c4-4b66-9f62-de694984a146
-- title:
--   Tie LDA: length quot span pow
-- statement:
--   The Tie LDA construction uses the length quot span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L304-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L304-L310

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module

theorem Formalism.L2.Pj.QAt.TieLDA.length_quot_span_pow {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {p : R} (hp : Irreducible p) (e : ℕ) : Module.length R (R ⧸ R ∙ p ^ e) = e := by sorry
