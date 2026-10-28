-- Prove2me | Theorems.Thm_BonusSeason_Periodic_lemma_1
-- name    : BonusSeason.Periodic.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:53.936963+00:00
-- url     : https://prove2.me/theorems/07e4d207-2c5a-43de-a92d-1a9ddf0884de
-- title:
--   Lemma 1, p. 11 (PDF 12) — a vacant firm's matching likelihood rises, an unemployed worker's falls, in labor market depth
-- statement:
--   Let $m$ be a matching function satisfying Assumption A1. For $M^0,N^0>0$ write $n^0=N^0/M^0$ for the labor market depth. Then the matching likelihoods depend only on depth,
--   $$\frac{m(M^0,N^0)}{M^0}=m(1,n^0),\qquad \frac{m(M^0,N^0)}{N^0}=\frac{m(1,n^0)}{n^0},$$
--   and $n\mapsto m(1,n)$ is strictly increasing while $n\mapsto m(1,n)/n$ is strictly decreasing on $(0,\infty)$.
--
--   This is the mechanism by which periodic fluctuations in the numbers searching translate into fluctuations of the matching likelihoods of firms and workers.
--
--   **Formalization Note** "Increasing/decreasing" are strict, matching the strict reading of A1.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), p. 11 (PDF 12), Lemma 1; eqs. (2)–(3), p. 10 (PDF 11)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Lemma 1, p. 11: with `n⁰ = N⁰/M⁰` the labor market depth, `f = m(M⁰,N⁰)/M⁰ = m(1, n⁰)` and
`g = m(M⁰,N⁰)/N⁰ = m(1, n⁰)/n⁰` ((2)–(3)); `f` is increasing and `g` decreasing in `n⁰`. -/
theorem lemma_1 (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m) :
    (∀ M0 N0 : ℝ, 0 < M0 → 0 < N0 →
      m M0 N0 / M0 = m 1 (N0 / M0) ∧ m M0 N0 / N0 = m 1 (N0 / M0) / (N0 / M0)) ∧
    StrictMonoOn (fun n => m 1 n) (Set.Ioi 0) ∧
    StrictAntiOn (fun n => m 1 n / n) (Set.Ioi 0) := by sorry
end BonusSeason.Periodic
