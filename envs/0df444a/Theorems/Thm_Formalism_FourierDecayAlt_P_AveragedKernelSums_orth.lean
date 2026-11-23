-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_orth
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:51.901107+00:00
-- url     : https://prove2.me/theorems/f065a867-e437-46f2-bfe3-4d39a198b453
-- title:
--   Averaged Kernel Sums: orth
-- statement:
--   The Averaged Kernel Sums construction uses the orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L271-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L271-L298

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

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.orth (hψ : ∀ r ∈ R, ψ r = 1) {P : AddSubgroup K} (hRP : R.toAddSubgroup ≤ P)
    (Tf : Finset (K ⧸ R.toAddSubgroup)) (hTf : ∀ x, x ∈ Tf ↔ Quotient.out x ∈ P) {c z₀ : K}
    (hc : c ∈ R) (hz : z₀ ∈ P) (hne : ψ (z₀ * c) ≠ 1) :
    ∑ x ∈ Tf, ψ (Quotient.out x * c) = 0 := by sorry
