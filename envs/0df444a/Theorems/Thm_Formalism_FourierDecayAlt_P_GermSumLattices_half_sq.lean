-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_half_sq
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.half_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:44.86437+00:00
-- url     : https://prove2.me/theorems/a5839779-d4ba-447e-9f9e-07a94e5148a4
-- title:
--   Germ Sum Lattices: half sq
-- statement:
--   The Germ Sum Lattices construction uses the half sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L193-L198

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}

theorem Formalism.FourierDecayAlt.P.GermSumLattices.half_sq (A : ℝ) (hA : 0 < A) (m : ℕ) :
    A ^ ((m : ℝ) ^ 2 / 2) * A ^ ((m : ℝ) ^ 2 / 2) = A ^ (m ^ 2) := by sorry
