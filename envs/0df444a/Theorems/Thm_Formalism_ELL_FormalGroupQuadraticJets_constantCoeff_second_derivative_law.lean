-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_constantCoeff_second_derivative_law
-- name    : Formalism.ELL.FormalGroupQuadraticJets.constantCoeff_second_derivative_law
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:48.646638+00:00
-- url     : https://prove2.me/theorems/9af803a7-6863-4742-9d39-d6d9e741409f
-- title:
--   Formal Group Quadratic Jets: constant Coeff second derivative law
-- statement:
--   The Formal Group Quadratic Jets construction uses the constant Coeff second derivative law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L179-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L179-L191

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.ELL.FormalGroupQuadraticJets.constantCoeff_second_derivative_law (F : FormalGroup (Formalism.G.unitBall K)) (φ : PowerSeries K) :
    PowerSeries.constantCoeff ((invD F)^[2] φ) =
      ccd 1 (FK F).toPowerSeries *
        (ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries) *
            PowerSeries.constantCoeff (PowerSeries.derivative K φ) +
          ccd 1 (FK F).toPowerSeries *
            PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ))) := by sorry
