-- Prove2me | Theorems.Thm_BookProof_ChapterDutchBook_payoff_single
-- name    : BookProof.ChapterDutchBook.payoff_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:07:37.544882+00:00
-- url     : https://prove2.me/theorems/9dd0710a-2dd7-42e1-acd4-95e9e7dcfcac
-- title:
--   `BookProof.ChapterDutchBook.payoff_single` (Pr : Finset Ω → ℝ) (A₀ : Finset Ω) (s₀ : ℝ) (ω : Ω) : payoff Pr ![A₀] ![s₀] ω = s₀ * (betIndicator A₀ ω - Pr A₀)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDutchBook`.
--
--   `BookProof.ChapterDutchBook.payoff_single` (Pr : Finset Ω → ℝ) (A₀ : Finset Ω) (s₀ : ℝ) (ω : Ω) : payoff Pr ![A₀] ![s₀] ω = s₀ * (betIndicator A₀ ω - Pr A₀)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDutchBook.payoff_single`.

-- Generated from ChapterDutchBook.lean — theorem BookProof.ChapterDutchBook.payoff_single
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook


open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

theorem BookProof.ChapterDutchBook.payoff_single (Pr : Finset Ω → ℝ) (A₀ : Finset Ω) (s₀ : ℝ) (ω : Ω) :
    payoff Pr ![A₀] ![s₀] ω = s₀ * (betIndicator A₀ ω - Pr A₀) := by sorry
