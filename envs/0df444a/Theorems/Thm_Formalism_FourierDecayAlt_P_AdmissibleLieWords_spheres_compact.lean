-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_spheres_compact
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.spheres_compact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:25:36.66382+00:00
-- url     : https://prove2.me/theorems/9538de49-05aa-434a-a64e-93c54d82f0c7
-- title:
--   Admissible Lie Words: spheres compact
-- statement:
--   The Admissible Lie Words construction uses the spheres compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Sq2UnitOfEqOneOfSq2EqDiv.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Sq2UnitOfEqOneOfSq2EqDiv.lean#L54-L62

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.spheres_compact (m m' : ℕ) :
    IsCompact {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by sorry
