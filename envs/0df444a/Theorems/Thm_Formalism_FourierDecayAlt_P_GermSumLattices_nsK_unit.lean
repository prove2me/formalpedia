-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_nsK_unit
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.nsK_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:00.014692+00:00
-- url     : https://prove2.me/theorems/1e32bdd0-9fe5-4257-9ece-8e9e13174fa1
-- title:
--   Germ Sum Lattices: ns K unit
-- statement:
--   The Germ Sum Lattices construction uses the ns K unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L244-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L244-L250

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
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)

theorem Formalism.FourierDecayAlt.P.GermSumLattices.nsK_unit (hMM : MM R) (h h' : Point K) (z : Kˣ) :
    NsK R ψ (m + 1) h h' (z : K) = ((modK R (z : K) ^ (m ^ 2 + m) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) z) := by sorry
