-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_exists_bornFiber_card_eq_two_pow
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:30:46.468161+00:00
-- url     : https://prove2.me/theorems/02d9e1ec-d0d2-47d9-b1c1-627bd7227327
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow` {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : ∃ p : ↥(stdSimplex ℝ (Fin n)), Nat.card ↥(bornMapSphere n ⁻¹' {p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow` {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : ∃ p : ↥(stdSimplex ℝ (Fin n)), Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow
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

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.exists_bornFiber_card_eq_two_pow {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ p : ↥(stdSimplex ℝ (Fin n)),
      Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ k := by sorry
