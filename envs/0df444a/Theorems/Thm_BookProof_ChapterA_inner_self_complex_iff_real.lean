-- Prove2me | Theorems.Thm_BookProof_ChapterA_inner_self_complex_iff_real
-- name    : BookProof.ChapterA.inner_self_complex_iff_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:39:25.040977+00:00
-- url     : https://prove2.me/theorems/96507c3b-b196-40e0-bb68-fa253884ecf5
-- title:
--   `BookProof.ChapterA.inner_self_complex_iff_real` (T : H₁ → H₂) : (∀ x, (inner ℂ (T x) (T x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (∀ x, (inner ℝ (T x) (T x) : ℝ) = (inner ℝ x x : ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1Prop5`.
--
--   `BookProof.ChapterA.inner_self_complex_iff_real` (T : H₁ → H₂) : (∀ x, (inner ℂ (T x) (T x) : ℂ) = (inner ℂ x x : ℂ)) ↔ (∀ x, (inner ℝ (T x) (T x) : ℝ) = (inner ℝ x x : ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.inner_self_complex_iff_real`.

-- Generated from ChapterA1Prop5.lean — theorem BookProof.ChapterA.inner_self_complex_iff_real
import Mathlib
import Definitions.Def_ChapterA1Prop5
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace





attribute [local instance] InnerProductSpace.rclikeToReal

theorem BookProof.ChapterA.inner_self_complex_iff_real (T : H₁ → H₂) :
    (∀ x, (inner ℂ (T x) (T x) : ℂ) = (inner ℂ x x : ℂ)) ↔
    (∀ x, (inner ℝ (T x) (T x) : ℝ) = (inner ℝ x x : ℝ)) := by sorry
