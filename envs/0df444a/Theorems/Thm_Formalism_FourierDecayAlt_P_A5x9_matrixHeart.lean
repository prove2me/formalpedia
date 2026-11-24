-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_matrixHeart
-- name    : Formalism.FourierDecayAlt.P.A5x9.matrixHeart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:08.952146+00:00
-- url     : https://prove2.me/theorems/2f981561-8be6-4e28-a47b-0c9478128a89
-- title:
--   A5x9: matrix Heart
-- statement:
--   The A5x9 construction uses the matrix Heart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1371-L1401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1371-L1401

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

theorem Formalism.FourierDecayAlt.P.A5x9.matrixHeart {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
    (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (n n' : ℕ) (hn : n = n') (k : ℕ) (hk : k + 2 ≤ n)
    (Z₀ : Matrix (Fin n) (Fin n) K) (Z₀' : Matrix (Fin n') (Fin n') K)
    (hd : IsUnit Z₀.det) (hd' : IsUnit Z₀'.det)
    (he : ∀ a b : Fin n, k < a.val → b.val + 1 = n → Z₀⁻¹ a b = 0)
    (he' : ∀ a b : Fin n', k < a.val → b.val + 1 = n' → Z₀'⁻¹ a b = 0) :
    ∃ (X : Type) (rel : X → Submodule R (Fin n → R) → Submodule R (Fin n' → R) → Prop),
      (∀ p p', IsPP R k p → IsPP R k p' → IsInt R (Z₀ * p) → IsInt R (Z₀' * p') →
        Nonempty ({φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p') //
          φ ∈ isoZZ R (Z₀ * p) (Z₀' * p') ∧ InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ∧
            ¬ InTT R k (Z₀ * p) (Z₀' * p') φ} ≃
          {x : X // rel x (latZ R (Z₀ * p)) (latZ R (Z₀' * p'))})) ∧
      (∀ x : X, ∃ σ σ', IsPP R k σ ∧ IsPP R k σ' ∧ ψ (sUp σ - sUp σ') ≠ 1 ∧
        ∀ p p', IsPP R k p → IsPP R k p' → IsInt R (Z₀ * p) → IsInt R (Z₀' * p') →
          rel x (latZ R (Z₀ * p)) (latZ R (Z₀' * p')) →
          IsInt R (Z₀ * (σ * p)) ∧ IsInt R (Z₀' * (σ' * p')) ∧
            rel x (latZ R (Z₀ * (σ * p))) (latZ R (Z₀' * (σ' * p')))) := by sorry
