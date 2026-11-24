-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block_index_last_val_eq
-- name    : Formalism.FourierDecayAlt.P.Ux6.block_index_last_val_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:28:43.498292+00:00
-- url     : https://prove2.me/theorems/8f21a8ac-543e-4757-8fea-26e2580a2b47
-- title:
--   Ux6: block index last val eq
-- statement:
--   The Ux6 construction uses the block index last val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L21-L22

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
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux6.block_index_last_val_eq (a : Fin j) : ((eB k j ρ) (Sum.inr a)).val = j + (2 * ρ + k + 1) + a.val := by sorry
