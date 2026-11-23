-- Prove2me | Theorems.Thm_DedekindZeta_Theta_sum_embeddings_mul
-- name    : DedekindZeta.Theta.sum_embeddings_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:11:07.620997+00:00
-- url     : https://prove2.me/theorems/8052b1d3-201a-45a2-91bf-95c6ab338081
-- title:
--   Theta: sum embeddings mul
-- statement:
--   The sum over all complex embeddings `∑_{σ : K →+* ℂ} σ b · σ a` equals the
--   image of the `ℚ`-trace `Tr_{K/ℚ}(b·a)` under `algebraMap ℚ ℂ`
--   (`trace_eq_sum_embeddings`, reindexed from `K →ₐ[ℚ] ℂ` to `K →+* ℂ`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L405-L411
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L405-L411

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.sum_embeddings_mul (b a : K) :
    (∑ σ : K →+* ℂ, σ b * σ a) = algebraMap ℚ ℂ (Algebra.trace ℚ K (b * a)) := by sorry
