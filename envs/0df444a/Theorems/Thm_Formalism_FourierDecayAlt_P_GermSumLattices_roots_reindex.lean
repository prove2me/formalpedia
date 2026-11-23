-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_roots_reindex
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.roots_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:13.910221+00:00
-- url     : https://prove2.me/theorems/4d4625c7-ab63-47c1-956b-a4191fb4c096
-- title:
--   Germ Sum Lattices: roots reindex
-- statement:
--   The Germ Sum Lattices construction uses the roots reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L100-L114

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

theorem Formalism.FourierDecayAlt.P.GermSumLattices.roots_reindex (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite) (D z₀ : Kˣ) (hz₀ : z₀ ^ (m + 1) = D)
    (G : Kˣ → ℂ) : ∑ z ∈ (hroots D).toFinset, G z = ∑ ζ ∈ μ, G (ζ * z₀) := by sorry
