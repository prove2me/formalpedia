-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_bad_iff
-- name    : Formalism.FourierDecayAlt.P.A5x9.cnt_bad_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:49.522885+00:00
-- url     : https://prove2.me/theorems/8479f3c0-7e63-413d-ade3-d152b76a11bd
-- title:
--   A5x9: cnt bad iff
-- statement:
--   The A5x9 construction uses the cnt bad iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L869-L944
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L869-L944

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.cnt_bad_iff (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det)
    (p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (hp' : IsPP R k p')
    (hZ : IsInt R (Z₀ * p)) (hfin : Finite (coker R (Z₀ * p)))
    (φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p')) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀')
    (hC : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y)
    (hT : InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ) (D : Matrix (Fin n) (Fin n) K)
    (hL : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      abelian₂ R k Z₀' y = D *ᵥ abelian₂ R k Z₀ x) :
    ¬ InTT R k (Z₀ * p) (Z₀' * p') φ ↔
      ∃ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
        abelian₂ R k Z₀ x = 0 ∧ lamTil R Z₀' k y - lamTil R Z₀ k x ∉ R := by sorry
