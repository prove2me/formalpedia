-- Prove2me | Theorems.Thm_AKSZigZag_section8_theorem
-- name    : AKSZigZag.section8_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:15.937434+00:00
-- url     : https://prove2.me/theorems/abc50ecb-b661-4cc8-be83-d7c5cdd5f4de
-- title:
--   §8 Theorem, p.7 — after every completed cycle $\Delta_r<\alpha^{3r+40}$ and $\delta<\alpha^{30}$
-- statement:
--   There is a number $a\le15$ of ZigZag repetitions per cycle with the following property. Under the standing assumptions below, run the zig-zag algorithm on any input permutation. Then after every completed cycle $t\in\{0,\dots,\log_2 n\}$ (for $t=0$, after the initial $\varepsilon$-nearsort), the errors computed with the intervals of time $t$ satisfy
--   $$
--   \text{(1)}\ \ \Delta_r<\alpha^{3r+40}\quad(r\ge1),\qquad\text{(2)}\ \ \delta<\alpha^{30}.
--   $$
--
--
--   The standing assumptions of §8 apply: $A$ is large ($A\ge A_0$, a power of $2$), $\varepsilon$ is small in terms of $A$ ($0<\varepsilon<\varepsilon_0$), $n$ is a power of $2$, and $\alpha=1/A$. Each $\mathrm{ns}_m$ may be any standard $\varepsilon$-nearsort network on $m$ registers.
--
--   At time $\log_2 n$ every node holds a single register, so $\delta<1$ means that every element is in its own register: the network sorts.
--
--   Differences from the source:
--   - reading: ZigZag is repeated a times, where a ≤ 15 (§6, p.6) → ∃ a with 1 ≤ a ≤ 15, quantified before A, ε and n; reason: the paper never fixes a; it is a parameter of the algorithm, chosen once
--   - reading: α small (A large), ε sufficiently small in terms of α; α never defined → ∃ A₀, ∀ A ≥ A₀ a power of 2, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); α = 1/A; reason: the standing assumption of §8, p.7, in quantifier form; the proofs use α = 1/A (|J′| > |J|α/2 in Lemma 1, the α/4 extreme interval and 4Aδ < 1 from δ < α² in the Remark, p.8)
--   - generalization: the algorithm with the ε-nearsort of §4 → any family of standard ε-nearsort networks ns m; reason: the proof uses only the ε-nearsort property; the §4 networks are one such family
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8 Theorem, p.7

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_RegisterAssignment
import Definitions.Def_AKSZigZag_zigzag
import Definitions.Def_AKSZigZag_Errors

namespace AKSZigZag

open AKSSorting.Core

/-- **The §8 Theorem** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.7): "Theorem. After
every completed cycle, we have (1) Δr < α^(3r+40), r ≥ 1 and (2) δ < α³⁰".

For some number `a ≤ 15` of ZigZag repetitions per cycle: for `A` large, `ε` small (in terms of
`A`), every power of 2 `n`, every family of standard ε-nearsort networks and every input
permutation, after every completed cycle `t ∈ {0, …, log₂ n}` (`t = 0`: after the initial
ε-nearsort) the configuration satisfies `Δ_r < α^{3r+40}` for every `r ≥ 1` and `δ < α³⁰`, with
the intervals of time `t`.

**Formalization Note.** The standing assumptions of §8, p.7 ("we will assume that α is
small (A is large), and ε is sufficiently small in terms of α") are `∃ A₀, ∀ A ≥ A₀` and
`∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`, with `α = 1/A` (α is never defined; the proofs use `α = 1/A`). `A`
and `n` are powers of 2 (§5). `ns m` is any standard ε-nearsort network on `m` registers. The
errors `Δ_r`, `δ` at time `t` are `Delta A n t r`, `delta A n t`, computed for a configuration
`y : Fin n → Fin n` (register ↦ content) with the intervals of time `t`.
`a` is the paper's "ZigZag is repeated a times, where a ≤ 15" (§6, p.6); the paper never fixes it,
so it is quantified first, before `A`, `ε` and `n`. -/
theorem section8_theorem :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 15 ∧
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → (∃ k, A = 2 ^ k) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ n : ℕ, (∃ k, n = 2 ^ k) →
    ∀ ns : (m : ℕ) → ComparatorNetwork m, (∀ m, IsStandard (ns m) ∧ IsNearsort ε (ns m)) →
    ∀ x : Fin n → Fin n, Function.Bijective x →
    ∀ t : ℕ, t ≤ Nat.log 2 n →
      (∀ r : ℕ, 1 ≤ r →
        Delta A n t r ((runNet A a ns n t).eval x) < (1 / (A : ℝ)) ^ (3 * r + 40)) ∧
      delta A n t ((runNet A a ns n t).eval x) < (1 / (A : ℝ)) ^ 30 := by sorry

end AKSZigZag
