-- Prove2me | Theorems.Thm_AKSZigZag_lemma_4
-- name    : AKSZigZag.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:06.439644+00:00
-- url     : https://prove2.me/theorems/c3cc95a5-c84c-49a3-8e21-b4b5a049232c
-- title:
--   Lemma 4, p.8 — after a completed cycle $\delta<10(A\varepsilon+\sum_{r\ge1}(4A)^r\Delta_r)<\alpha^{30}$
-- statement:
--   There is a number $a\le15$ of ZigZag repetitions per cycle (the same kind of choice as in the §8 Theorem) with the following property. Run the algorithm on an input permutation and let $t+1\le\log_2 n$. Suppose that after cycle $t$ (intervals of time $t$) the bounds of the §8 Theorem hold:
--   $$
--   \Delta_r<\alpha^{3r+40}\ (r\ge1),\qquad \delta<\alpha^{30}.
--   $$
--   Then after cycle $t+1$, with the errors $\Delta_r,\delta$ computed with the intervals of time $t+1$,
--   $$
--   \delta<10\Big(A\varepsilon+\sum_{r\ge1}(4A)^r\Delta_r\Big)<\alpha^{30}.
--   $$
--
--
--   The standing assumptions of §8 apply: $A$ is large ($A\ge A_0$, a power of $2$), $\varepsilon$ is small in terms of $A$ ($0<\varepsilon<\varepsilon_0$), $n$ is a power of $2$, and $\alpha=1/A$. Each $\mathrm{ns}_m$ may be any standard $\varepsilon$-nearsort network on $m$ registers.
--
--   Lemmas 1–3 let $\delta$ grow during a cycle; this lemma restores the bound on $\delta$ at its end, closing the induction.
--
--   Differences from the source:
--   - reading: After a completed cycle, we have (3) → after cycle t + 1, given the bounds (1) and (2) after cycle t; reason: Lemma 4 is proved inside the induction of the §8 Theorem (p.8: 'Assume the theorem holds for some t and prove it for t+1'); its bound < α³⁰ uses the inductive hypothesis
--   - encoding: Σ_{r≥1} (4A)^r Δr → the sum over 1 ≤ r ≤ 2(t+1); reason: at time t+1 two nodes are at tree distance at most 2(t+1), so Δr = 0 for larger r and the series is this finite sum
--   - reading: the number a of ZigZag repetitions (§6, a ≤ 15) → ∃ a with 1 ≤ a ≤ 15, quantified first; reason: the paper never fixes a; Lemma 4 is about the algorithm with the paper's a, as in the §8 Theorem, and its proof (p.9, 'the next Zig step will exchange all foreign elements') needs enough ZigZag repetitions in the cycle, so it is not claimed for every a ≤ 15
--   - reading: α small (A large), ε sufficiently small in terms of α; α never defined → ∃ A₀, ∀ A ≥ A₀ a power of 2, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); α = 1/A; reason: the standing assumption of §8, p.7, in quantifier form; the proofs use α = 1/A (|J′| > |J|α/2 in Lemma 1, the α/4 extreme interval and 4Aδ < 1 from δ < α² in the Remark, p.8)
--   - generalization: the algorithm with the ε-nearsort of §4 → any family of standard ε-nearsort networks ns m; reason: the proof uses only the ε-nearsort property; the §4 networks are one such family
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, Lemma 4, p.8

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_RegisterAssignment
import Definitions.Def_AKSZigZag_zigzag
import Definitions.Def_AKSZigZag_Errors

namespace AKSZigZag

open AKSSorting.Core

/-- **Lemma 4** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.8): "After a completed cycle, we
have (3) δ < 10(Aε + Σ_{r≥1} (4A)^r Δr) < α³⁰".

Inside the induction of the §8 Theorem: run the algorithm on an input permutation `x`; if after
cycle `t` (`t + 1 ≤ log₂ n`) the bounds (1) `Δ_r < α^{3r+40}` for all `r ≥ 1` and (2)
`δ < α³⁰` hold (time-`t` intervals), then after cycle `t + 1` (time-`(t+1)` intervals)
`δ < 10(Aε + Σ_{r≥1} (4A)^r Δ_r)` and `10(Aε + Σ_{r≥1} (4A)^r Δ_r) < α³⁰`.

**Formalization Note.** The standing assumptions of §8, p.7 ("we will assume that α is
small (A is large), and ε is sufficiently small in terms of α") are `∃ A₀, ∀ A ≥ A₀` and
`∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`, with `α = 1/A` (α is never defined; the proofs use `α = 1/A`). `A`
and `n` are powers of 2 (§5). `ns m` is any standard ε-nearsort network on `m` registers. The
errors `Δ_r`, `δ` at time `t` are `Delta A n t r`, `delta A n t`, computed for a configuration
`y : Fin n → Fin n` (register ↦ content) with the intervals of time `t`.
The sum runs over `1 ≤ r ≤ 2(t+1)`: at time `t + 1` two nodes are at tree distance at most
`2(t+1)`, so `Δ_r = 0` for larger `r` and the paper's series is this finite sum.
The number `a ≤ 15` of ZigZag repetitions is quantified as in the §8 Theorem (`∃ a`, first): the
lemma is about the algorithm with the paper's `a`, which the paper never fixes, and its proof
(p.9: "If the bound … is less than α³⁵|J| after a Zag step, then the next Zig step …") relies
on enough ZigZag repetitions in the cycle, so it is not claimed for every `a ≤ 15`. -/
theorem lemma_4 :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 15 ∧
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → (∃ k, A = 2 ^ k) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ n : ℕ, (∃ k, n = 2 ^ k) →
    ∀ ns : (m : ℕ) → ComparatorNetwork m, (∀ m, IsStandard (ns m) ∧ IsNearsort ε (ns m)) →
    ∀ x : Fin n → Fin n, Function.Bijective x →
    ∀ t : ℕ, t + 1 ≤ Nat.log 2 n →
    (∀ r : ℕ, 1 ≤ r →
      Delta A n t r ((runNet A a ns n t).eval x) < (1 / (A : ℝ)) ^ (3 * r + 40)) →
    delta A n t ((runNet A a ns n t).eval x) < (1 / (A : ℝ)) ^ 30 →
      delta A n (t + 1) ((runNet A a ns n (t + 1)).eval x) <
          10 * (A * ε + ∑ r ∈ Finset.Icc 1 (2 * (t + 1)),
            (4 * (A : ℝ)) ^ r * Delta A n (t + 1) r ((runNet A a ns n (t + 1)).eval x)) ∧
      10 * (A * ε + ∑ r ∈ Finset.Icc 1 (2 * (t + 1)),
            (4 * (A : ℝ)) ^ r * Delta A n (t + 1) r ((runNet A a ns n (t + 1)).eval x)) <
          (1 / (A : ℝ)) ^ 30 := by sorry

end AKSZigZag
