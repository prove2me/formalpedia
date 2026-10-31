-- Prove2me | Theorems.Thm_CapacityGames_lemma_2
-- name    : CapacityGames.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:49.240378+00:00
-- url     : https://prove2.me/theorems/cf6237be-b69e-4f1e-ad7e-5c3e17c568e6
-- title:
--   Lemma 2: under submodularity (6), $N^*(f)\setminus\{i\}\subseteq N^*_{-i}(f)$
-- statement:
--   Let $N$ be a finite set and $f$ a real-valued set function on the subsets of $N$ satisfying the submodularity inequalities (6). Write $N^*(f)=\{j: f(N)>f(N\setminus\{j\})\}$ and $N^*_{-i}(f)=\{j: f(N\setminus\{i\})>f(N\setminus\{i,j\})\}$. Then for every $i\in N$,
--   $$N^*(f)\setminus\{i\}\subseteq N^*_{-i}(f).$$
--
--   With $f=\Pi^*_{\mathcal C}$ this is Lemma 2 of the paper: every supplier that contributes to the optimal supply chain profit still contributes when some other supplier $i$ is unavailable. The proof of Theorem 2 uses it to evaluate the buyer's profit when supplier $i$ is excluded, (A-3).
--
--   Differences from the source:
--   - generalization: $\Pi^*_{\mathcal C}$ under Assumption 3 → any set function $f$ satisfying (6); reason: the proof uses only (6), and $\Pi^*_{\mathcal C}$ under Assumption 3 is an instance.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §4, Lemma 2, p.10 (proof App. A.4, p.27)

import Mathlib
import Definitions.Def_CapacityGames_SetFunction

namespace CapacityGames

/-- **Lemma 2**, Anderson–Chen–Shao, *Capacity Games with Supply Function Competition*,
arXiv:1905.11084v1, §4, p.10 (proof App. A.4, p.27): under the submodularity property (6), for
every `i ∈ N`, `N*(f) ∖ {i} ⊆ N*_{−i}(f)`.

**Formalization Note.** Stated for an arbitrary set function `f : Finset N → ℝ` satisfying (6);
the paper's statement is the case `f = Π*_C`, where `N*(f)` and `N*_{−i}(f)` are `N*(𝒞)` and
`N*_{−i}(𝒞)`. -/
theorem lemma_2 {N : Type*} [Fintype N] [DecidableEq N] (f : Finset N → ℝ)
    (hf : LocalSubmodular f) (i : N) :
    (contribSet f).erase i ⊆ contribSetExcept f i := by sorry

end CapacityGames
