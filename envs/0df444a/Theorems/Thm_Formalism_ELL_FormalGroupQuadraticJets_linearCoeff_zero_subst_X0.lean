-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_zero_subst_X0
-- name    : Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_zero_subst_X0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:51.296453+00:00
-- url     : https://prove2.me/theorems/657973f2-46e5-4a50-99ae-85513a19af5f
-- title:
--   Formal Group Quadratic Jets: linear Coeff zero subst X0
-- statement:
--   The Formal Group Quadratic Jets construction uses the linear Coeff zero subst X0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L57-L62

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

theorem Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_zero_subst_X0 (g : PowerSeries K) :
    ccd 0 (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff 1 g := by sorry
