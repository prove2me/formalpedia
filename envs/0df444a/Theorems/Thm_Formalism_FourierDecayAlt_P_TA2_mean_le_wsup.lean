-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_mean_le_wsup
-- name    : Formalism.FourierDecayAlt.P.TA2.mean_le_wsup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:58.816866+00:00
-- url     : https://prove2.me/theorems/e5b3cac6-0007-4757-aced-5c7a51c63b89
-- title:
--   TA2: mean le wsup
-- statement:
--   The TA2 construction uses the mean le wsup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L108-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L108-L124

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2

theorem Formalism.FourierDecayAlt.P.TA2.mean_le_wsup {W : Type} [Fintype W] (len : W → ℕ) (B : ℕ) (th : W × W → ℝ)
    (hth : IsProb2 len B th) (g : W → ℝ) :
    ∑ x, th x * g x.1 ≤ wsup len B g ∧ ∑ x, th x * g x.2 ≤ wsup len B g := by sorry
