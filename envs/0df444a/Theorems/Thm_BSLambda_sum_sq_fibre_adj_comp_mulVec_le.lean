-- Prove2me | Theorems.Thm_BSLambda_sum_sq_fibre_adj_comp_mulVec_le
-- name    : BSLambda.sum_sq_fibre_adj_comp_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:59.247796+00:00
-- url     : https://prove2.me/theorems/8492687c-1ae3-4ef2-a005-617e861412bd
-- title:
--   BSLambda: sum sq fibre adj comp mul Vec le
-- statement:
--   **The fibrewise bound.**  On the fibre of `topBits g` over `b`, the master identity writes
--   `A_{f∘g} ψ` as a sum of `#W` vectors whose norms `sum_sq_fibre_summand_le` controls; Minkowski's
--   inequality then bounds the fibre by `lambda(g)` times the value at `b` of `A_f` applied to the
--   vector of fibre norms of `ψ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L352-L376
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L352-L376

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

theorem BSLambda.sum_sq_fibre_adj_comp_mulVec_le (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (b : Input W) :
    ∑ x : Input (W × V), (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2
      ≤ lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := by sorry
