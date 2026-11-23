-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_vol_eq
-- name    : Formalism.FourierDecayAlt.P.PairingConjugationLemmas.vol_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:36.971792+00:00
-- url     : https://prove2.me/theorems/af034747-5de7-4d69-84ba-055c52f1690f
-- title:
--   Pairing Conjugation Lemmas: vol eq
-- statement:
--   The Pairing Conjugation Lemmas construction uses the vol eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean#L209-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean#L209-L214

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

theorem Formalism.FourierDecayAlt.P.PairingConjugationLemmas.vol_eq : ∃ c : NNReal, 0 < c ∧
    (volume : Measure (V f)) = c • Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ)) := by sorry
