-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_intH
-- name    : Formalism.FourierDecayAlt.P.Ux6.intH
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:23:25.17037+00:00
-- url     : https://prove2.me/theorems/2d2d9ca9-adab-4564-8697-bc54a1d1ae8b
-- title:
--   Ux6: int H
-- statement:
--   The Ux6 construction uses the int H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L487-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L487-L507

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6

theorem Formalism.FourierDecayAlt.P.Ux6.intH (p s : ℕ) (σ : Equiv.Perm (Fin p)) (a : ℝ) (h1 : ((s * (p * 2) : ℕ) : ℝ) < a)
    (h2 : ((p * (s * 2) : ℕ) : ℝ) < a) (h3 : ((p * p * 2 : ℕ) : ℝ) < a) :
    Integrable (fun η : XiH p s σ => wtH η ^ (-a)) (muXiH p s σ) := by sorry
