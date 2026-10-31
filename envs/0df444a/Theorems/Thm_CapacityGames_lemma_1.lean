-- Prove2me | Theorems.Thm_CapacityGames_lemma_1
-- name    : CapacityGames.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:48.924833+00:00
-- url     : https://prove2.me/theorems/551fff4f-070a-4e54-a764-0e4f4f57a908
-- title:
--   Lemma 1: under submodularity (6), $f(N)-f(S)\ge\sum_{i\in N\setminus S}(f(N)-f(N\setminus\{i\}))$
-- statement:
--   Let $N$ be a finite set and $f$ a real-valued set function on the subsets of $N$ satisfying the submodularity inequalities (6): for every $S\subseteq N$ and $i,j\in S$, $i\ne j$,
--   $$f(S)-f(S\setminus\{i\})\le f(S\setminus\{j\})-f(S\setminus\{i,j\}).$$
--   Then for every $S\subseteq N$,
--   $$f(N)-f(S)\ge\sum_{i\in N\setminus S}\big(f(N)-f(N\setminus\{i\})\big).\quad(7)$$
--
--   With $f=\Pi^*_{\mathcal C}$ this is Lemma 1 of the paper: the loss in supply chain profit from removing the suppliers outside $S$ is at least the sum of their individual marginal contributions. It is the inequality that bounds the buyer's profit in (A-2) and the deviating supplier's profit on p.30.
--
--   Differences from the source:
--   - generalization: $\Pi^*_{\mathcal C}$ under Assumption 3 → any set function $f$ satisfying (6); reason: the proof uses only (6), and $\Pi^*_{\mathcal C}$ under Assumption 3 is an instance.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §4, Lemma 1, (7), p.10 (proof App. A.3, p.27)

import Mathlib
import Definitions.Def_CapacityGames_SetFunction

namespace CapacityGames

/-- **Lemma 1**, Anderson–Chen–Shao, *Capacity Games with Supply Function Competition*,
arXiv:1905.11084v1, §4, p.10 (proof App. A.3, p.27): under the submodularity property (6), for
every `S ⊆ N`,
`f(N) − f(S) ≥ Σ_{i∈N∖S} (f(N) − f(N ∖ {i}))` (7).

**Formalization Note.** Stated for an arbitrary set function `f : Finset N → ℝ` satisfying (6)
(`LocalSubmodular`); the paper's statement is the case `f = Π*_C`. `N` is `Finset.univ`. -/
theorem lemma_1 {N : Type*} [Fintype N] [DecidableEq N] (f : Finset N → ℝ)
    (hf : LocalSubmodular f) (S : Finset N) :
    ∑ i ∈ Finset.univ \ S, (f Finset.univ - f (Finset.univ.erase i)) ≤
      f Finset.univ - f S := by sorry

end CapacityGames
