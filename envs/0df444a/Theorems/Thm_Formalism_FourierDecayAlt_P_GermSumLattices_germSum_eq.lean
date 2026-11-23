-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_germSum_eq
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.germSum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:45.689527+00:00
-- url     : https://prove2.me/theorems/93a98229-b313-45f6-8e96-76345d7887f3
-- title:
--   Germ Sum Lattices: germ Sum eq
-- statement:
--   The Germ Sum Lattices construction uses the germ Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L92-L98

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
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)

theorem Formalism.FourierDecayAlt.P.GermSumLattices.germSum_eq (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite) (t c : Kˣ)
    (f : Kˣ → ℂ) : germSum R ψ m γ t c f =
      ((modK R (t : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
        ∑ z ∈ (hroots ((-t) ^ m * c)).toFinset, germCoef R ψ m γ t z * f z := by sorry
