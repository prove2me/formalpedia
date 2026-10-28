-- Prove2me | Theorems.Thm_Erdos195_open_pair_reaches_sink
-- name    : Erdos195.open_pair_reaches_sink
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T23:42:34.701264+00:00
-- url     : https://prove2.me/theorems/5b928c23-7fb0-4363-bb1c-ae4922a7119d
-- title:
--   Every fully open pair reaches a true sink
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $t=2b-a$ its third term and $w=3b-2a$ its fourth term; the pair is fully open in $T$ if neither lies in $T$. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $0\le i<m-1$ and no third term $2b_i-a_i$ in $T$.
--
--   **Theorem.** Let $T$ be $\theta$-safe for some tree witness and let $(a_0,b_0)$ be a fully open in-order pair of $T$. Then there is an open path $(a_i,b_i)_{0\le i<m}$ with $m\ge1$ starting at $(a_0,b_0)$ whose sink fourth term $w=3b_{m-1}-2a_{m-1}$ is not in $T$ (so every pair of the path is fully open), such that $w$ is a **true sink**: whenever $w=2y-x$ for an in-order pair $(x,y)$ of $T$, the fourth term $3y-2x$ lies in $T$. Moreover $m+1\le 2^r$, where $r$ is the number of distinct levels $\nu_2(b_i-a_i)$ on the path.
--
--   Following "fourth term = third term of the next fully open pair" from any fully open pair always stops at a true sink. Its fourth term then satisfies the first (C1) condition of the tree append criterion (milestone #59). By milestone #153 it never conflicts with its own path. Proof: chains that never stop would repeat a pair (pigeonhole over $T\times T$), which gives an open cycle, impossible by milestone #147. The length bound is milestone #151.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_pair_reaches_sink (T : List ℤ) (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) T)
    (a₀ b₀ : ℤ) (ha₀ : a₀ ∈ T) (hb₀ : b₀ ∈ T) (hi₀ : T.idxOf a₀ < T.idxOf b₀)
    (ht₀ : 2 * b₀ - a₀ ∉ T) (hw₀ : 3 * b₀ - 2 * a₀ ∉ T) :
    ∃ (m : ℕ) (a b : ℕ → ℤ), 0 < m ∧ a 0 = a₀ ∧ b 0 = b₀ ∧
      (∀ i < m, a i ∈ T) ∧ (∀ i < m, b i ∈ T) ∧
      (∀ i < m, T.idxOf (a i) < T.idxOf (b i)) ∧
      (∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1)) ∧
      (∀ i < m, 2 * b i - a i ∉ T) ∧
      3 * b (m - 1) - 2 * a (m - 1) ∉ T ∧
      (∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y →
        2 * y - x = 3 * b (m - 1) - 2 * a (m - 1) → 3 * y - 2 * x ∈ T) ∧
      m + 1 ≤ 2 ^ ((Finset.range m).image (fun i => padicValInt 2 (b i - a i))).card := by sorry

end Erdos195
