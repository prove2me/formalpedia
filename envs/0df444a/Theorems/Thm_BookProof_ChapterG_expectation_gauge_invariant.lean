-- Prove2me | Theorems.Thm_BookProof_ChapterG_expectation_gauge_invariant
-- name    : BookProof.ChapterG.expectation_gauge_invariant
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:25:21.211647+00:00
-- url     : https://prove2.me/theorems/3bef5684-ddd0-47ad-a94d-9eb6f893fd66
-- title:
--   `BookProof.ChapterG.expectation_gauge_invariant` {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (U : V →L[ℂ] V) (hU : U ∈ unitary (V →L[ℂ] V)) (A : V
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.expectation_gauge_invariant` {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (U : V →L[ℂ] V) (hU : U ∈ unitary (V →L[ℂ] V)) (A : V →L[ℂ] V) (hA : A * U = U * A) (Ψ : V) : ⟪U Ψ, A (U Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.expectation_gauge_invariant`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.expectation_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix

theorem BookProof.ChapterG.expectation_gauge_invariant {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (U : V →L[ℂ] V) (hU : U ∈ unitary (V →L[ℂ] V))
    (A : V →L[ℂ] V) (hA : A * U = U * A) (Ψ : V) :
    ⟪U Ψ, A (U Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ := by sorry
