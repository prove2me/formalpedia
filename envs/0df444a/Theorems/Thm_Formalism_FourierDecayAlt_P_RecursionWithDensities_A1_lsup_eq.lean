-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_lsup_eq
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.lsup_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:07.046539+00:00
-- url     : https://prove2.me/theorems/e4820cd8-605e-46b9-8773-04674c0242d5
-- title:
--   A1: lsup eq
-- statement:
--   The A1 construction uses the lsup eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L295-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L295-L300

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.lsup_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type} [Fintype W]
    (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (len : W → ℕ) (Kl : ℕ) (Φ : W → Pt E → H) (j : ℕ) :
    lsup (D' D Sg Th) len Kl Sg Φ j = lsup D len Kl Sg Φ j := by sorry
