-- Prove2me | Theorems.Thm_BookProof_MassGap_exp_conj_eq_self
-- name    : BookProof.MassGap.exp_conj_eq_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:35:44.4707+00:00
-- url     : https://prove2.me/theorems/1993ea99-03e6-43e7-815e-1324cfa6e765
-- title:
--   Conjugating an observable by `exp Y` is trivial when the observable commutes with `Y`: `exp Y · Obs · exp(-Y) = Obs`
-- statement:
--   Conjugating an observable by `exp Y` is trivial when the observable commutes
--   with `Y`: `exp Y · Obs · exp(-Y) = Obs`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MassGap.exp_conj_eq_self` (module `BookProof.MassGap`), line-linked source: `ChapterMassGap.lean` lines 63–72.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMassGap.lean#L63-L72

-- Generated from ChapterMassGap.lean — theorem BookProof.MassGap.exp_conj_eq_self
import Mathlib
import Definitions.Def_ChapterMassGap
open BookProof.MassGap

















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem BookProof.MassGap.exp_conj_eq_self {Obs Y : 𝔸} (h : Commute Obs Y) :
    NormedSpace.exp Y * Obs * NormedSpace.exp (-Y) = Obs := by sorry
