-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianMixture_vonNeumann_abelian_class_mixture
-- name    : BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-05T14:08:40.045204+00:00
-- url     : https://prove2.me/theorems/08b35e1e-a787-4ef4-9a20-6c0fc62eb96b
-- title:
--   `BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture` : (multOp (μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianMixture`.
--
--   `BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture` : (multOp (μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture`.

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture
import Mathlib
import Definitions.Def_ChapterAbelianMixture
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_one
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_mul
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_conj
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal













open BookProof.ChapterLinftyMultiplication

theorem BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture :
    (multOp (μ := mixtureMeasure) (fun _ : ℝ => (1 : ℂ)) memLp_top_one
        = ContinuousLinearMap.id ℂ (Lp ℂ 2 mixtureMeasure)) ∧
    (∀ (φ ψ : ℝ → ℂ) (hφ : MemLp φ ⊤ mixtureMeasure) (hψ : MemLp ψ ⊤ mixtureMeasure),
      (multOp φ hφ).comp (multOp ψ hψ) = (multOp ψ hψ).comp (multOp φ hφ)) ∧
    (∀ (φ ψ : ℝ → ℂ) (hφ : MemLp φ ⊤ mixtureMeasure) (hψ : MemLp ψ ⊤ mixtureMeasure),
      (multOp φ hφ).comp (multOp ψ hψ)
        = multOp (fun x => φ x * ψ x) (memLp_top_mul hφ hψ)) ∧
    (∀ (φ : ℝ → ℂ) (hφ : MemLp φ ⊤ mixtureMeasure) (f g : Lp ℂ 2 mixtureMeasure),
      inner ℂ (multOp φ hφ f) g
        = inner ℂ f (multOp (fun x => (starRingEnd ℂ) (φ x)) (memLp_top_conj hφ) g)) ∧
    (∀ (φ : ℝ → ℂ) (hφ : MemLp φ ⊤ mixtureMeasure), multOp φ hφ = 0 ↔ φ =ᵐ[mixtureMeasure] 0) := by sorry
