-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_eq_17
-- name    : BoundedEntropyGames.ConvRate.eq_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:41.200923+00:00
-- url     : https://prove2.me/theorems/510fd6ce-c1e8-401e-ba25-161cfbe63cbb
-- title:
--   (17), p. 19 — the block lengths $N_{n,i}$ and their properties
-- statement:
--   Let $n\ge0$ and $f\ge1$ be integers, and split $n$ stages into $f$ blocks with lengths $N_{n,i}=\lfloor n/f\rfloor+1$ for $i=1,\dots,k_n$ and $N_{n,i}=\lfloor n/f\rfloor$ for $i=k_n+1,\dots,f$, where $k_n=n\bmod f$. Then
--
--   1. the lengths are nonincreasing in $i$ (so $N_{n,i-1}\ge N_{n,i}$);
--   2. $N_{n,i}\ge n/f-1$ for every block;
--   3. $\sum_{i=1}^{f}N_{n,i}=n$;
--   4. $N_{n,1}\le n/f+1$.
--
--   These are the facts about the block structure used in (25), (30) and (34)–(35).
--
--   **Formalization Note** Blocks are indexed $0,\dots,f-1$ (block $i$ of the paper is index $i-1$).
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 19, (17); p. 21 (after (25)); p. 23 (before (30)); p. 24 (after (35))

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- (17), p. 19, and the facts drawn from it on pp. 21, 23, 24 (0-based block index):
the block lengths are nonincreasing, each is at least `n/f - 1`, they sum to `n`, and the
first is at most `n/f + 1`. -/
theorem eq_17 (n f : ℕ) (hf : 1 ≤ f) :
    (∀ i j : ℕ, i ≤ j → j < f → blockLen n f j ≤ blockLen n f i) ∧
    (∀ i < f, (n : ℝ) / f - 1 ≤ blockLen n f i) ∧
    ∑ i ∈ Finset.range f, blockLen n f i = n ∧
    (blockLen n f 0 : ℝ) ≤ (n : ℝ) / f + 1 := by sorry

end BoundedEntropyGames.ConvRate
