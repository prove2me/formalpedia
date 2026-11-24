-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_pderiv_one_subst_X0
-- name    : Formalism.ELL.FormalGroupQuadraticJets.pderiv_one_subst_X0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:05.72802+00:00
-- url     : https://prove2.me/theorems/f0dc76eb-b934-4d41-9b4b-5fd8fc159f1f
-- title:
--   Formal Group Quadratic Jets: pderiv one subst X0
-- statement:
--   The Formal Group Quadratic Jets construction uses the pderiv one subst X0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L33-L37

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

theorem Formalism.ELL.FormalGroupQuadraticJets.pderiv_one_subst_X0 (g : PowerSeries K) :
    MvPowerSeries.pderiv K 1 (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
      = 0 := by sorry
