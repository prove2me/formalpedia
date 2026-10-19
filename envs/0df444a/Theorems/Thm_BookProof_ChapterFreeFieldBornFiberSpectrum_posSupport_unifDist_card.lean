-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_posSupport_unifDist_card
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:38.344332+00:00
-- url     : https://prove2.me/theorems/67239152-6070-4b4d-8517-1432e09c9e6c
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card` {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : (posSupport (unifDist n k)).card = k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card` {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : (posSupport (unifDist n k)).card = k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card
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

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (posSupport (unifDist n k)).card = k := by sorry
