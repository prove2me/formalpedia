-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_quad_bound
-- name    : Formalism.FourierDecayAlt.P.Sz4.quad_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:06.674809+00:00
-- url     : https://prove2.me/theorems/d9581c39-9efc-4125-8f60-88f8bb962d74
-- title:
--   Sz4: quad bound
-- statement:
--   The Sz4 construction uses the quad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L172-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L172-L197

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.quad_bound (J : ℕ) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2 ≤
      7 / 64 * (J : ℝ) := by sorry
