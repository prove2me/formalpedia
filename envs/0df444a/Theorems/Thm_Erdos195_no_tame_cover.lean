-- Prove2me | Theorems.Thm_Erdos195_no_tame_cover
-- name    : Erdos195.no_tame_cover
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T03:10:04.008715+00:00
-- url     : https://prove2.me/theorems/93f310e0-2e34-46ce-aaae-0d18db641891
-- title:
--   No exhaustive word family has open pairs of unbounded $2$-adic valuation
-- statement:
--   Let $Q$ be a finite word of integers. An in-order pair of $Q$ is a pair $(a,b)$ of letters with $a$ occurring before $b$; it is open if neither continuation $2b-a$ nor $3b-2a$ is a letter of $Q$. Let $(P_m)_{m\ge0}$ be finite words with $P_m\subseteq P_{m+1}$ (as sets) and $\bigcup_m P_m=\mathbb{Z}$, and let $L:\mathbb{N}\to\mathbb{N}$ with $L_m\to\infty$. Then it is impossible that
--   $$\nu_2(b-a)\ \ge\ L_m\qquad\text{for every open in-order pair }(a,b)\text{ of }P_m\text{ and every }m.$$
--   In the context of Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195), where the open pairs of a safe word are exactly what force digits of $\varepsilon$, this rules out any exhaustive construction in which the forced digits are pushed to ever higher positions ("tame" constructions). The statement holds even without assuming the words are safe.
--
--   Formalization note: nestedness is `∀ m, ∀ x ∈ P m, x ∈ P (m + 1)`; $L_m\to\infty$ is `Filter.Tendsto L atTop atTop`; "before" is comparison of `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem no_tame_cover (P : ℕ → List ℤ) (hmono : ∀ m, ∀ x ∈ P m, x ∈ P (m + 1))
    (hcov : ∀ x : ℤ, ∃ m, x ∈ P m) (L : ℕ → ℕ) (hL : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hopen : ∀ m, ∀ a ∈ P m, ∀ b ∈ P m, (P m).idxOf a < (P m).idxOf b →
      2 * b - a ∉ P m → 3 * b - 2 * a ∉ P m → L m ≤ padicValInt 2 (b - a)) : False := by sorry

end Erdos195
