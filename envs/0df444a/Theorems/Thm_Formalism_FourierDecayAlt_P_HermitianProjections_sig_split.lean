-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_sig_split
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.sig_split
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:55.813486+00:00
-- url     : https://prove2.me/theorems/cda4585c-0c56-4b03-a5fe-c7a3b7f2a5c3
-- title:
--   Hermitian Projections: sig split
-- statement:
--   The Hermitian Projections construction uses the sig split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L170-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L170-L328

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections

theorem Formalism.FourierDecayAlt.P.HermitianProjections.sig_split {p q : ℕ} (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (ψ₁ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ)) (h₁ : ∀ c, ψ₁ c = 0 → (star c ⬝ᵥ (G *ᵥ c)).re ≤ 0)
    (ψ₂ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin q → ℂ)) (h₂ : ∀ c, ψ₂ c = 0 → 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUnit Q.det ∧ Qᴴ * G * Q = fromBlocks 1 0 0 (-1) := by sorry
