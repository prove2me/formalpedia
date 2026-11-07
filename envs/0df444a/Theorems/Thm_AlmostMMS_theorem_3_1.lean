-- Prove2me | Theorems.Thm_AlmostMMS_theorem_3_1
-- name    : AlmostMMS.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:53.387205+00:00
-- url     : https://prove2.me/theorems/3e2f8b7c-c5ef-4f6c-9999-622694d636c4
-- title:
--   Theorem 3.1 — the normalized form of the main result
-- statement:
--   For every fixed $\varepsilon\in(0,1)$ and integer $q\ge3$ there is $n(\varepsilon,q)$ such that for every $n\ge n(\varepsilon,q)$ the following holds. Take $m$ items and $n$ additive agents, and $1\le d\le(1-\varepsilon)n$, with $\mathrm{MMS}(M,v_i,d)=1$ for every agent $i$. Then there are $d$ distinct agents $I$ and an allocation $(B_i)_{i\in I}$ of $M$ to $I$ with
--   $$
--   v_i(B_i)\ge 1-\frac2q\qquad\text{for every } i\in I.
--   $$
--   Here $n$ is the number of agents and $d$ the number selected. The threshold is on the agent count, so small $d$ is covered. Theorem 1.1 follows after rescaling and setting aside agents with share $0$.
--
--   Differences from the source:
--   - encoding: an allocation as a partition of M → a map A from items into I, with bundle A⁻¹(i); reason: same partitions; every item goes to an agent of I
--   - encoding: additive valuations with v(∅) = 0, monotone → the published `LittleCharity.MMS.IsAdditive` (additivity and nonnegativity); reason: equivalent for additive set functions
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 3.1, p.20

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace AlmostMMS

open Finset

/-- **Theorem 3.1, p.20** (Theorem 1.1 restated). Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): for every fixed `ε ∈ (0, 1)` and
integer `q ≥ 3` there is `n(ε, q)` such that for every `n ≥ n(ε, q)`, if all `n` agents are additive with
`MMS(M, v_i, d) = 1` and `1 ≤ d ≤ (1 - ε) n`, then some `d` agents and an allocation of `M` to them give
each of them value at least `1 - 2/q`.

**Formalization Note.** From here on `n` is the number of agents and `d` the number selected. The
allocation is a map `A` from items into `I`; the threshold `n₀` is on the agent count, and `m` and `d` are
chosen after it. -/
theorem theorem_3_1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (q : ℕ) (hq : 3 ≤ q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (m d : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
      LittleCharity.MMS.IsAdditive v → 1 ≤ d → (d : ℝ) ≤ (1 - ε) * (n : ℝ) →
      (∀ i, LittleCharity.MMS.mms (v i) d univ = 1) →
      ∃ I : Finset (Fin n), I.card = d ∧ ∃ A : Fin m → Fin n, (∀ b, A b ∈ I) ∧
        ∀ i ∈ I, 1 - 2 / (q : ℝ) ≤ v i (univ.filter fun b => A b = i) := by sorry

end AlmostMMS
