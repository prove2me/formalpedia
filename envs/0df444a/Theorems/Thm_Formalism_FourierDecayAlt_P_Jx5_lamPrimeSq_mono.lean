-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_lamPrimeSq_mono
-- name    : Formalism.FourierDecayAlt.P.Jx5.lamPrimeSq_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:43.252826+00:00
-- url     : https://prove2.me/theorems/e2f52ccc-6b65-4ab9-b55d-777b20229c7c
-- title:
--   Jx5: lam Prime Sq mono
-- statement:
--   The Jx5 construction uses the lam Prime Sq mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L31-L36

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

theorem Formalism.FourierDecayAlt.P.Jx5.lamPrimeSq_mono (m i : ℕ) {C C' κ N I A TT : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (hκ : 0 ≤ κ)
    (hN : 0 ≤ N) (hI : 0 ≤ I) (hA : 0 ≤ A) :
    Sz.lamPrimeSq m i C κ N I A TT ≤ Sz.lamPrimeSq m i C' κ N I A TT := by sorry
