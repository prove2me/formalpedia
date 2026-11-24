-- Prove2me | Theorems.Thm_DimdPolyShowcaseChallenge_stable_phase_retrieval
-- name    : DimdPolyShowcaseChallenge.stable_phase_retrieval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:45:25.897482+00:00
-- url     : https://prove2.me/theorems/0f47dbf2-9ccf-4f8a-8d75-4005f56b61b5
-- title:
--   Dimd Poly Showcase Challenge: stable phase retrieval
-- statement:
--   Stable phase retrieval for Gaussian `L²` limits of finite Hermite-Fock polynomials.
--
--   This is the main qualitative statement.  The comparison signal `Q` is an element
--   of the Gaussian `L²` closure of the finite Hermite-Fock polynomials.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly.lean#L126-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly.lean#L126-L144

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyShowcaseChallenge
variable {d : ℕ}

theorem DimdPolyShowcaseChallenge.stable_phase_retrieval
    (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ TrueHermitePolys κ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ Q ∈ TrueHermiteFunctions κ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖P z - θ * Q z‖ ^ 2 ∂ γ
            ≤ M ^ 2 * ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ γ := by sorry
