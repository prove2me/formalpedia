-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_asymSector
-- name    : BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-19T14:34:48.286843+00:00
-- url     : https://prove2.me/theorems/e5a07a2b-b80a-4a58-bf6d-dba1d1faf002
-- title:
--   `BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x)) (hesa : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn (redDom (asymProj U) D) (redOp T (isReducingProjection_asymProj hU2 hUi) (commutes_asymProj hTU))
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_ReducedEsa_isReducingProjection_asymProj
import Theorems.Thm_BookProof_ReducedEsa_commutes_asymProj
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

theorem BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y)
    {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x))
    (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom (asymProj U) D)
      (redOp T (isReducingProjection_asymProj hU2 hUi) (commutes_asymProj hTU)) := by sorry
