-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_card_alt
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.card_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:53.578799+00:00
-- url     : https://prove2.me/theorems/e237654d-e1e6-4bc5-8540-e86acf2c0ec8
-- title:
--   Averaged Kernel Sums: card alt
-- statement:
--   The Averaged Kernel Sums construction uses the card alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L236-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L236-L248

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.card_alt {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P) :
    Nat.card {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ P} = R.toAddSubgroup.relIndex P := by sorry
