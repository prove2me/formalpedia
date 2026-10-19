-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_bornFiber_card_mono
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:42.64774+00:00
-- url     : https://prove2.me/theorems/f6b068f7-c62d-46df-b54c-55065ec825d7
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono` {p q : ↥(stdSimplex ℝ (Fin n))} (h : posSupport (p : Fin n → ℝ) ⊆ posSupport (q : Fin n → ℝ)) : Nat.card ↥(bornMap
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono` {p q : ↥(stdSimplex ℝ (Fin n))} (h : posSupport (p : Fin n → ℝ) ⊆ posSupport (q : Fin n → ℝ)) : Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ Nat.card ↥(bornMapSphere n ⁻¹' {q})
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
open BookProof.ChapterFreeFieldBornFiberSpectrum


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_mono {p q : ↥(stdSimplex ℝ (Fin n))}
    (h : posSupport (p : Fin n → ℝ) ⊆ posSupport (q : Fin n → ℝ)) :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ Nat.card ↥(bornMapSphere n ⁻¹' {q}) := by sorry
