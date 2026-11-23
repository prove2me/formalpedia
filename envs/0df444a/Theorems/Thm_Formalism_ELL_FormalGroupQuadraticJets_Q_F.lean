-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_Q_F
-- name    : Formalism.ELL.FormalGroupQuadraticJets.Q_F
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:39.910238+00:00
-- url     : https://prove2.me/theorems/877899a1-319c-4061-92a5-d5e1ecfbe8cc
-- title:
--   Formal Group Quadratic Jets: Q F
-- statement:
--   The Formal Group Quadratic Jets construction uses the Q F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L109-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L109-L122

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
variable {K : Type*} [CommRing K]

theorem Formalism.ELL.FormalGroupQuadraticJets.Q_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Q (F.subst ![x, y]) =
      ccd 0 F * Q x + ccd 0 x * (ccd 0 (MvPowerSeries.pderiv K 0 F) * ccd 1 x +
          ccd 1 (MvPowerSeries.pderiv K 0 F) * ccd 1 y) +
        ccd 1 F * Q y + ccd 0 y * (ccd 0 (MvPowerSeries.pderiv K 1 F) * ccd 1 x +
          ccd 1 (MvPowerSeries.pderiv K 1 F) * ccd 1 y) := by sorry
