-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_back
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.back
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:34.92273+00:00
-- url     : https://prove2.me/theorems/e9ecfb80-c26a-459b-b99d-f1cb2407093f
-- title:
--   Germ Sum Lattices: back
-- statement:
--   The Germ Sum Lattices construction uses the back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L322-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L322-L332

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

theorem Formalism.FourierDecayAlt.P.GermSumLattices.back {cr : K ⧸ R.toAddSubgroup → Kˣ} {S : Set K} (t₁ : Kˣ)
    (hSfin : {x | (cr x : K) ∈ S}.Finite) (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    {i1 : DecidablePred fun x => (cr x : K) ∈ S}
    {i2 : ∀ x, DecidablePred fun z : Kˣ => z ^ (m + 1) = (-t₁) ^ m * cr x} (G : Kˣ → ℂ) :
    ∑ᶠ x, (if (cr x : K) ∈ S then
      ∑ᶠ z : Kˣ, (if z ^ (m + 1) = (-t₁) ^ m * cr x then G z else 0) else 0) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset, G z := by sorry
