-- Prove2me | Theorems.Thm_AKSZigZag_lemma_1
-- name    : AKSZigZag.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:45.224979+00:00
-- url     : https://prove2.me/theorems/dc13290c-9850-49b0-9dd4-85011e05e5b7
-- title:
--   Lemma 1, p.8 — register reassignment: $\Delta'_r\le6A\Delta_{r-4}$, $\delta'<6A(\delta+\varepsilon)$ (corrected: $\le$ in the $\Delta$ clause)
-- statement:
--   Run the algorithm on an input permutation, and let $y$ be the configuration at the end of cycle $t$, where $t+1\le\log_2 n$ (for $t=0$, after the initial $\varepsilon$-nearsort). Let $\Delta_r,\delta$ be the errors of $y$ computed with the intervals of time $t$, and $\Delta'_r,\delta'$ those of the same configuration computed with the intervals of time $t+1$. Then
--   $$
--   \Delta'_r\le6A\,\Delta_{r-4}\quad(r\ge6),\qquad \delta'<6A(\delta+\varepsilon).
--   $$
--
--
--   The standing assumptions of §8 apply: $A$ is large ($A\ge A_0$, a power of $2$), $\varepsilon$ is small in terms of $A$ ($0<\varepsilon<\varepsilon_0$), $n$ is a power of $2$, and $\alpha=1/A$. Each $\mathrm{ns}_m$ may be any standard $\varepsilon$-nearsort network on $m$ registers.
--
--   The reassignment at the start of every cycle damages the errors at most by these factors; the ZigZag steps then repair them.
--
--   Differences from the source:
--   - correction: Δ′r < 6AΔr−4, r ≥ 6 → Δ′r ≤ 6AΔr−4; reason: at the sorted input every Δ is 0 at every time, so the strict inequality reads 0 < 0
--   - reading: the errors before the register reassignment (any configuration) → the configuration at the end of a completed cycle of the algorithm; reason: for an arbitrary configuration the δ′ clause is false: with δ = 0 and the contents of an old interval shuffled inside it, a new interval that is a proper piece of at most half the old one can hold only foreign elements, so δ′ ≥ 1 > 6A(0 + ε); the ε in 6A(δ+ε) comes from the cycle's last ε-nearsort
--   - generalization: the algorithm with its number a ≤ 15 of ZigZag repetitions (§6), which the paper never fixes → every a with 1 ≤ a ≤ 15, quantified first; reason: the reassignment does not depend on a (the proof of Lemma 1, p.8, uses only the interval geometry and the last ε-nearsort of the cycle); the paper's a is one such a
--   - reading: α small (A large), ε sufficiently small in terms of α; α never defined → ∃ A₀, ∀ A ≥ A₀ a power of 2, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); α = 1/A; reason: the standing assumption of §8, p.7, in quantifier form; the proofs use α = 1/A (|J′| > |J|α/2 in Lemma 1, the α/4 extreme interval and 4Aδ < 1 from δ < α² in the Remark, p.8)
--   - generalization: the algorithm with the ε-nearsort of §4 → any family of standard ε-nearsort networks ns m; reason: the proof uses only the ε-nearsort property; the §4 networks are one such family
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, Lemma 1, p.8

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_RegisterAssignment
import Definitions.Def_AKSZigZag_zigzag
import Definitions.Def_AKSZigZag_Errors

namespace AKSZigZag

open AKSSorting.Core

/-- **Lemma 1** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.8), *corrected* (`≤` in the
`Δ` clause): "If Δr and δ are the errors before the register reassignment, then for the
corresponding numbers Δ'r and δ' after reassignment we have the estimates Δ'r < 6AΔr-4, r ≥ 6
and δ' < 6A(δ+ε)".

Take the configuration `y` at the end of cycle `t` of the algorithm (`t = 0`: after the
initial ε-nearsort), `t + 1 ≤ log₂ n`, on any input permutation `x`. Let `Δ_r, δ` be its errors
with the intervals of time `t`, and `Δ'_r, δ'` those of the same contents with the intervals of
time `t + 1`. Then `Δ'_r ≤ 6AΔ_{r-4}` for `r ≥ 6` and `δ' < 6A(δ + ε)`.

**Formalization Note.** The standing assumptions of §8, p.7 ("we will assume that α is
small (A is large), and ε is sufficiently small in terms of α") are `∃ A₀, ∀ A ≥ A₀` and
`∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`, with `α = 1/A` (α is never defined; the proofs use `α = 1/A`). `A`
and `n` are powers of 2 (§5). `ns m` is any standard ε-nearsort network on `m` registers. The
errors `Δ_r`, `δ` at time `t` are `Delta A n t r`, `delta A n t`, computed for a configuration
`y : Fin n → Fin n` (register ↦ content) with the intervals of time `t`.
The configuration is the algorithm's, not an arbitrary one: for arbitrary contents the `δ'`
clause is false (`δ = 0` with the contents of an interval shuffled inside it, which the
reassignment splits). The strict `<` of the `Δ` clause is false at the sorted input (both sides
`0`) and is corrected to `≤`. -/
theorem lemma_1 :
    ∀ a : ℕ, 1 ≤ a → a ≤ 15 →
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → (∃ k, A = 2 ^ k) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ n : ℕ, (∃ k, n = 2 ^ k) →
    ∀ ns : (m : ℕ) → ComparatorNetwork m, (∀ m, IsStandard (ns m) ∧ IsNearsort ε (ns m)) →
    ∀ x : Fin n → Fin n, Function.Bijective x →
    ∀ t : ℕ, t + 1 ≤ Nat.log 2 n →
      (∀ r : ℕ, 6 ≤ r →
        Delta A n (t + 1) r ((runNet A a ns n t).eval x) ≤
          6 * A * Delta A n t (r - 4) ((runNet A a ns n t).eval x)) ∧
      delta A n (t + 1) ((runNet A a ns n t).eval x) <
        6 * A * (delta A n t ((runNet A a ns n t).eval x) + ε) := by sorry

end AKSZigZag
