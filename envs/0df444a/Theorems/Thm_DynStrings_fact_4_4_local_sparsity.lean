-- Prove2me | Theorems.Thm_DynStrings_fact_4_4_local_sparsity
-- name    : DynStrings.fact_4_4_local_sparsity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:40.501542+00:00
-- url     : https://prove2.me/theorems/ec5a6862-935c-412d-a354-263cc286d75f
-- title:
--   Fact 4.4 — local sparsity: $|B_k\cap I|<2+(4|I|-4)/\ell_{k+1}$ and $|S_k|<1+4n/\ell_{k+1}$
-- statement:
--   Let $S$ be a string of length $n$, let $k\ge0$, and fix any choice of the orders. For every non-empty integer interval $I\subseteq[0..n]$,
--
--   $$|B_k\cap I|<2+\frac{4|I|-4}{\ell_{k+1}},$$
--
--   where $B_k$ is the set of level-$k$ boundaries and $|I|$ the number of integers in $I$. In particular the level-$k$ word satisfies
--
--   $$|S_k|<1+\frac{4n}{\ell_{k+1}}.$$
--
--   Phrases are long on average: at level $k$ any window of the text contains about four boundaries per $\ell_{k+1}$ characters. This bounds the number of rounds and the length of the level words used throughout the analysis.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - reading: |I| for an interval I ⊆ [0..n] → the number of integers j − i + 1 of I = [i..j]; reason: |I| is a cardinality here; the length reading j − i is false at k = 0, n = 1, I = [0..1]
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Fact 4.4, p.16 (cited from KNO24, Lemma 3.8 and Corollary 3.9)

import Mathlib
import Definitions.Def_DynStrings_Parse

namespace DynStrings

/-- **Fact 4.4** (local sparsity, cited from [KNO24, Lemma 3.8 and Corollary 3.9]), p.16.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

For every string `S` of length `n`, every `k ≥ 0`, every choice of the orders, and every non-empty
interval `I = [i..j] ⊆ [0..n]`, `|B_k ∩ I| < 2 + (4|I| − 4)/ℓ_{k+1}`; in particular
`|S_k| < 1 + 4n/ℓ_{k+1}`.

**Formalization Note.** `|I|` is the number of integers in `I`, `j − i + 1`. -/
theorem fact_4_4_local_sparsity {α : Type} [DecidableEq α] (S : List α) (k : ℕ)
    (lt : ℕ → StrSym α → StrSym α → Prop) (hlt : IsOrderFamily lt) :
    (∀ i j : ℕ, i ≤ j → j ≤ S.length →
      ((boundaries lt S k ∩ Finset.Icc i j).card : ℝ) <
        2 + (4 * ((j - i + 1 : ℕ) : ℝ) - 4) / ell (k + 1)) ∧
    ((level lt S k).length : ℝ) < 1 + 4 * (S.length : ℝ) / ell (k + 1) := by sorry

end DynStrings
