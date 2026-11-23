-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_intLat_smul
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.intLat_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:14.133264+00:00
-- url     : https://prove2.me/theorems/1330e01b-2efb-4d5a-b10c-23a56d24a4a0
-- title:
--   Germ Sum Lattices: int Lat smul
-- statement:
--   The Germ Sum Lattices construction uses the int Lat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L304-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L304-L314

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

theorem Formalism.FourierDecayAlt.P.GermSumLattices.intLat_smul (Λ : AddSubgroup K) (Om : Set K) (F G : K → ℂ) (c : ℂ)
    (hF : ∀ z ∈ Om, F z = c * G z) : intLat R Λ Om F = c * intLat R Λ Om G := by sorry
