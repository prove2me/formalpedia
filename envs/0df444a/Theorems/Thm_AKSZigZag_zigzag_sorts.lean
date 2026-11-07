-- Prove2me | Theorems.Thm_AKSZigZag_zigzag_sorts
-- name    : AKSZigZag.zigzag_sorts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:46.120479+00:00
-- url     : https://prove2.me/theorems/07f2d7be-bd30-4b3f-b727-c65170acf27c
-- title:
--   §8, p.7 — the zig-zag network is a standard sorting network of depth $O(\log n)$
-- statement:
--   There is a number $a\le15$ of ZigZag repetitions per cycle with the following property. Under the standing assumptions below, the zig-zag network (the initial $\varepsilon$-nearsort, then the cycles $t=1,\dots,\log_2 n$):
--   1. uses only standard switches;
--   2. sorts every input (from every linearly ordered type);
--   3. has depth at most
--   $$
--   \operatorname{depth}(\mathrm{ns}_n)+2a\log_2 n\cdot\max_{m\le n}\operatorname{depth}(\mathrm{ns}_m).
--   $$
--
--
--   The standing assumptions of §8 apply: $A$ is large ($A\ge A_0$, a power of $2$), $\varepsilon$ is small in terms of $A$ ($0<\varepsilon<\varepsilon_0$), $n$ is a power of $2$, and $\alpha=1/A$. Each $\mathrm{ns}_m$ may be any standard $\varepsilon$-nearsort network on $m$ registers.
--
--   With the bounded-depth nearsorts of §§3–4, clause 3 is $O(\log n)$. Together with padding $n$ up to a power of $2$, this gives the headline theorem.
--
--   Differences from the source:
--   - generalization: the algorithm sorts → adds clause 1 (standard switches) and clause 3 (the depth of the construction); reason: both hold by construction (§7); dropping them gives the source's claim
--   - reading: ZigZag is repeated a times, where a ≤ 15 (§6, p.6) → ∃ a with 1 ≤ a ≤ 15, quantified before A, ε and n; reason: the paper never fixes a
--   - reading: α small (A large), ε sufficiently small in terms of α; α never defined → ∃ A₀, ∀ A ≥ A₀ a power of 2, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); α = 1/A; reason: the standing assumption of §8, p.7, in quantifier form; the proofs use α = 1/A (|J′| > |J|α/2 in Lemma 1, the α/4 extreme interval and 4Aδ < 1 from δ < α² in the Remark, p.8)
--   - generalization: the algorithm with the ε-nearsort of §4 → any family of standard ε-nearsort networks ns m; reason: the proof uses only the ε-nearsort property; the §4 networks are one such family
--   - generalization: the algorithm sorts permutations of 1,...,n ('We may assume the contents are also 1,...,n', p.3) → sorts every input from every linearly ordered type (Sorts); reason: permutations of 1..n are such inputs
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, p.7 ("The following theorem clearly implies that the algorithm sorts"), §7, p.7 (the algorithm)

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_RegisterAssignment
import Definitions.Def_AKSZigZag_zigzag
import Definitions.Def_AKSZigZag_Errors

namespace AKSZigZag

open AKSSorting.Core

/-- **The zig-zag network sorts** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.7): "The
following theorem clearly implies that the algorithm sorts (at time log n there are no errors
since δ < 1)."

For some number `a ≤ 15` of ZigZag repetitions per cycle: for `A` large, `ε` small (in terms of
`A`), every power of 2 `n` and every family `ns` of standard ε-nearsort networks, the zig-zag
network `zigzag A a ns n` (the initial ε-nearsort, then the cycles `t = 1, …, log₂ n`)
1. has only standard comparators,
2. sorts every input (`Sorts`: every input from every linearly ordered type, not only the
   permutations of `1, …, n` of the paper), and
3. has depth at most `depth(ns n) + 2a·log₂ n·max_{m ≤ n} depth(ns m)`.

**Formalization Note.** The standing assumptions of §8, p.7 ("we will assume that α is
small (A is large), and ε is sufficiently small in terms of α") are `∃ A₀, ∀ A ≥ A₀` and
`∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`, with `α = 1/A` (α is never defined; the proofs use `α = 1/A`). `A`
and `n` are powers of 2 (§5). `ns m` is any standard ε-nearsort network on `m` registers. The
errors `Δ_r`, `δ` at time `t` are `Delta A n t r`, `delta A n t`, computed for a configuration
`y : Fin n → Fin n` (register ↦ content) with the intervals of time `t`.
Clause 3 is the depth of the construction (one initial nearsort, then `2a` nearsort steps per
cycle, the parts of a step running in parallel); with bounded-depth nearsorts it is the paper's
`O(log n)`. -/
theorem zigzag_sorts :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 15 ∧
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → (∃ k, A = 2 ^ k) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ n : ℕ, (∃ k, n = 2 ^ k) →
    ∀ ns : (m : ℕ) → ComparatorNetwork m, (∀ m, IsStandard (ns m) ∧ IsNearsort ε (ns m)) →
      IsStandard (zigzag A a ns n) ∧ (zigzag A a ns n).Sorts ∧
      (zigzag A a ns n).depth ≤
        (ns n).depth + 2 * a * Nat.log 2 n * ((Finset.range (n + 1)).sup fun m => (ns m).depth) := by sorry

end AKSZigZag
