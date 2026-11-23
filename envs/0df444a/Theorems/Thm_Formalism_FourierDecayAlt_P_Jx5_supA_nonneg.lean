-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_supA_nonneg
-- name    : Formalism.FourierDecayAlt.P.Jx5.supA_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:55.643123+00:00
-- url     : https://prove2.me/theorems/74c78721-cfdd-40b3-ad24-776936ecd977
-- title:
--   Jx5: sup A nonneg
-- statement:
--   The Jx5 construction uses the sup A nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L38-L57

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5

theorem Formalism.FourierDecayAlt.P.Jx5.supA_nonneg {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
    (one : Bool) (w : ι) (hg : 0 < G.g) (hv : 0 < G.v) : 0 ≤ supA G de de' T T' l one w := by sorry
