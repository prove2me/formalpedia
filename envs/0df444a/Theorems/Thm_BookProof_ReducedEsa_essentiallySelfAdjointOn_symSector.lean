-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_symSector
-- name    : BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-19T14:34:44.967828+00:00
-- url     : https://prove2.me/theorems/34d4c3fe-b603-404e-8a4a-3584e325172a
-- title:
--   `BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x)) (hesa : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn (redDom (symProj U) D) (redOp T (isReducingProjection_symProj hU2 hUi) (commutes_symProj hTU))
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_ReducedEsa_isReducingProjection_symProj
import Theorems.Thm_BookProof_ReducedEsa_commutes_symProj
open BookProof.ReducedEsa



open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {P : F →ₗ[ℂ] F}
variable {D : Submodule ℂ F}
variable (T : D →ₗ[ℂ] F)
variable {T}
variable (U : F →ₗ[ℂ] F)
variable {U}

theorem BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y)
    {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x))
    (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom (symProj U) D)
      (redOp T (isReducingProjection_symProj hU2 hUi) (commutes_symProj hTU)) := by sorry
