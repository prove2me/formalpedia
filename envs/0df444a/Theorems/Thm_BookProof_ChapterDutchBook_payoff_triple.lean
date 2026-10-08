-- Prove2me | Theorems.Thm_BookProof_ChapterDutchBook_payoff_triple
-- name    : BookProof.ChapterDutchBook.payoff_triple
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:07:44.210857+00:00
-- url     : https://prove2.me/theorems/fcb0c231-4322-4820-a665-c4ff879c0ae2
-- title:
--   `BookProof.ChapterDutchBook.payoff_triple` (Pr : Finset Ω → ℝ) (A₀ A₁ A₂ : Finset Ω) (s₀ s₁ s₂ : ℝ) (ω : Ω) : payoff Pr ![A₀, A₁, A₂] ![s₀, s₁, s₂] ω = s₀ *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDutchBook`.
--
--   `BookProof.ChapterDutchBook.payoff_triple` (Pr : Finset Ω → ℝ) (A₀ A₁ A₂ : Finset Ω) (s₀ s₁ s₂ : ℝ) (ω : Ω) : payoff Pr ![A₀, A₁, A₂] ![s₀, s₁, s₂] ω = s₀ * (betIndicator A₀ ω - Pr A₀) + s₁ * (betIndicator A₁ ω - Pr A₁) + s₂ * (betIndicator A₂ ω - Pr A₂)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDutchBook.payoff_triple`.

-- Generated from ChapterDutchBook.lean — theorem BookProof.ChapterDutchBook.payoff_triple
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook


open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

theorem BookProof.ChapterDutchBook.payoff_triple (Pr : Finset Ω → ℝ) (A₀ A₁ A₂ : Finset Ω)
    (s₀ s₁ s₂ : ℝ) (ω : Ω) :
    payoff Pr ![A₀, A₁, A₂] ![s₀, s₁, s₂] ω =
      s₀ * (betIndicator A₀ ω - Pr A₀) + s₁ * (betIndicator A₁ ω - Pr A₁)
        + s₂ * (betIndicator A₂ ω - Pr A₂) := by sorry
