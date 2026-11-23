-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_eD_apply
-- name    : Formalism.FourierDecayAlt.P.PairingConjugationLemmas.eD_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:21.9729+00:00
-- url     : https://prove2.me/theorems/65d024b5-0950-4f7c-b1ac-1c7d62d836e3
-- title:
--   Pairing Conjugation Lemmas: e D apply
-- statement:
--   The Pairing Conjugation Lemmas construction uses the e D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean#L205-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean#L205-L205

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]

theorem Formalism.FourierDecayAlt.P.PairingConjugationLemmas.eD_apply (m : Fin (finrank ℤ La) → ℤ) : ((eD La m : dualSet La) : V f) = ψd La m := by sorry
