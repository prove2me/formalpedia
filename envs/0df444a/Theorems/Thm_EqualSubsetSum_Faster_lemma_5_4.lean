-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_5_4
-- name    : EqualSubsetSum.Faster.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:23:43.91323+00:00
-- url     : https://prove2.me/theorems/59c056cc-da2a-4509-97c6-9fce73e9b179
-- title:
--   Lemma 5.4 — rebalancing: F_t(u) ≤ 2^{c₀√t} a★^t (1 + u)
-- statement:
--   Let $(L_i)$ be a finite family of nonempty finite lists of pairs of positive reals, with $\mathcal V$ and $F_t$ as in the rebalancing recursion. There is a constant $c_0$, depending only on the lists, such that: if $\mathcal V(\tau)\le a_\star$ for every $\tau\in[0,1]$, then for all integers $t\ge0$ and reals $u>0$,
--   $$F_t(u)\le 2^{c_0\sqrt t}\,a_\star^{\,t}\,(1+u).$$
--   It controls the circuit degrees obtained by greedy rebalancing of block circuits (§5.4).
--
--   Differences from the source:
--   - encoding: a finite family (L_i) → a nonempty finite index type ι; reason: min_i over an empty family is undefined; the source's V and F_t presuppose a nonempty family
--   - encoding: c₀ depends only on the lists → ∃ c₀ quantified after the lists and before a★, t and u; reason: literal form of 'depends only on the lists'
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 35, Lemma 5.4

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Rebalancing

namespace EqualSubsetSum.Faster

/-- Lemma 5.4 (p. 35). For a finite (nonempty) family of nonempty finite lists of pairs of
positive reals there is `c₀`, depending only on the lists, such that whenever `V(τ) ≤ a★` for
every `τ ∈ [0, 1]`, `F_t(u) ≤ 2^{c₀ √t} a★^t (1 + u)` for all integers `t ≥ 0` and reals `u > 0`. -/
theorem lemma_5_4 {ι : Type} [Fintype ι] [Nonempty ι] (L : ι → List (ℝ × ℝ))
    (hne : ∀ i, L i ≠ []) (hpos : ∀ i, ∀ ab ∈ L i, 0 < ab.1 ∧ 0 < ab.2) :
    ∃ c₀ : ℝ, ∀ aStar : ℝ, (∀ τ ∈ Set.Icc (0 : ℝ) 1, Vfun L τ ≤ aStar) →
      ∀ (t : ℕ) (u : ℝ), 0 < u →
        Ffun L t u ≤ (2 : ℝ) ^ (c₀ * Real.sqrt t) * aStar ^ t * (1 + u) := by sorry

end EqualSubsetSum.Faster
