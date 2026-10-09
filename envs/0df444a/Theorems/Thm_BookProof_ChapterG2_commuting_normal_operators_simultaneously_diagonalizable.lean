-- Prove2me | Theorems.Thm_BookProof_ChapterG2_commuting_normal_operators_simultaneously_diagonalizable
-- name    : BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:50:51.543992+00:00
-- url     : https://prove2.me/theorems/826fdb02-925a-47c7-bc68-fcdd96985ccb
-- title:
--   `BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable` {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {ι : Type*} [Finit
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable` {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {ι : Type*} [Finite ι] (T : ι → H →ₗ[ℂ] H) (h_symm : ∀ i, (T i).IsSymmetric) (h_comm : ∀ i j, i ≠ j → Commute (T i) (T j)) : ⨆ (χ : ι → ℂ), ⨅ i, Module.End.eigenspace (T i) (χ i) = ⊤
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2


open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG2.commuting_normal_operators_simultaneously_diagonalizable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ι : Type*} [Finite ι]
    (T : ι → H →ₗ[ℂ] H) (h_symm : ∀ i, (T i).IsSymmetric)
    (h_comm : ∀ i j, i ≠ j → Commute (T i) (T j)) :
    ⨆ (χ : ι → ℂ), ⨅ i, Module.End.eigenspace (T i) (χ i) = ⊤ := by sorry
