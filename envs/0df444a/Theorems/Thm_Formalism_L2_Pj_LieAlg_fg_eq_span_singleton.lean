-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LieAlg_fg_eq_span_singleton
-- name    : Formalism.L2.Pj.LieAlg.fg_eq_span_singleton
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:02.954974+00:00
-- url     : https://prove2.me/theorems/da15ee73-1a0c-4945-8d2e-d3e0c3ee59cd
-- title:
--   Lie Alg: fg eq span singleton
-- statement:
--   The Lie Alg construction uses the fg eq span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L50-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem Formalism.L2.Pj.LieAlg.fg_eq_span_singleton (S : Submodule V K) (hS : S.FG) : ∃ t : K, S = span V {t} := by sorry
