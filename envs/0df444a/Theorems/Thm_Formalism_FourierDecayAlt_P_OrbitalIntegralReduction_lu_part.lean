-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_part
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_part
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:26.933575+00:00
-- url     : https://prove2.me/theorems/820faeac-5b6f-4734-b2ac-70742b75dd3a
-- title:
--   Orbital Integral Reduction: lu part
-- statement:
--   The Orbital Integral Reduction construction uses the lu part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L951-L980
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L951-L980

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_part (R : Subring K) (n : ℕ) (v : Pr n → K) :
    ∃! q : upUniG K n ⧸ intSub R (upUniG K n), ∃ r : Pr n → K, (∀ p, r p ∈ R) ∧
      v = lu_co (sec_m (Quotient.out q)) + lu_M (sec_m (Quotient.out q)) *ᵥ r := by sorry
