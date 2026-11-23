-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_quadraticJet_subst_X0
-- name    : Formalism.ELL.FormalGroupQuadraticJets.quadraticJet_subst_X0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:52.114016+00:00
-- url     : https://prove2.me/theorems/be85483d-da31-4150-9ef7-79f815c85841
-- title:
--   Formal Group Quadratic Jets: quadratic Jet subst X0
-- statement:
--   The Formal Group Quadratic Jets construction uses the quadratic Jet subst X0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L45-L49

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

theorem Formalism.ELL.FormalGroupQuadraticJets.quadraticJet_subst_X0 (g : PowerSeries K) :
    Q (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by sorry
