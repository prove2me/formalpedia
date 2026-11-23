-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_Q_phi
-- name    : Formalism.ELL.FormalGroupQuadraticJets.Q_phi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:47.165698+00:00
-- url     : https://prove2.me/theorems/7ae0ae39-846a-43ab-ae76-02010cc26060
-- title:
--   Formal Group Quadratic Jets: Q phi
-- statement:
--   The Formal Group Quadratic Jets construction uses the Q phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L83-L92

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

theorem Formalism.ELL.FormalGroupQuadraticJets.Q_phi (φ : PowerSeries K) {S : MvPowerSeries (Fin 2) K}
    (hS : MvPowerSeries.constantCoeff S = 0) :
    Q (φ.subst S) =
      PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) *
          ccd 1 S * ccd 0 S +
        PowerSeries.constantCoeff (PowerSeries.derivative K φ) * Q S := by sorry
