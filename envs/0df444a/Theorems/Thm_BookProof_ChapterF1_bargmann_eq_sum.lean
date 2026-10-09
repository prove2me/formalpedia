-- Prove2me | Theorems.Thm_BookProof_ChapterF1_bargmann_eq_sum
-- name    : BookProof.ChapterF1.bargmann_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:45:30.409805+00:00
-- url     : https://prove2.me/theorems/864a9231-5b23-4558-b307-0c6c5b289c8e
-- title:
--   `BookProof.ChapterF1.bargmann_eq_sum` (p q : ℂ[X]) {s : Finset ℕ} (hp : p.support ⊆ s) (hq : q.support ⊆ s) : bargmann p q = ∑ n ∈ s, (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.bargmann_eq_sum` (p q : ℂ[X]) {s : Finset ℕ} (hp : p.support ⊆ s) (hq : q.support ⊆ s) : bargmann p q = ∑ n ∈ s, (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n) * q.coeff n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.bargmann_eq_sum`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.bargmann_eq_sum
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.bargmann_eq_sum (p q : ℂ[X]) {s : Finset ℕ}
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    bargmann p q = ∑ n ∈ s, (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n) * q.coeff n := by sorry
