-- Prove2me | Theorems.Thm_AKSZigZag_lemma_2
-- name    : AKSZigZag.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:39.765395+00:00
-- url     : https://prove2.me/theorems/cbeeb81c-079c-4883-99f7-d8617b56f876
-- title:
--   Lemma 2, p.8 — one Zig or Zag step: $\Delta'_r\le8A(\Delta_r+\varepsilon\Delta_{r-2})$ (corrected: $\le$ for $r\ge3$)
-- statement:
--   Let $1\le t\le\log_2 n$, and let $y$ be any configuration (a permutation) whose error $\delta$ with the intervals of time $t$ satisfies $\delta<\alpha^2$. Let $y'$ be the configuration after one Zig step (the parts of $P_{t1}$) or one Zag step (the parts of $P_{t2}$) of cycle $t$. With $\Delta_r,\delta$ the errors of $y$ and $\Delta'_r,\delta'$ those of $y'$:
--   1. $\Delta'_r\le8A(\Delta_r+\varepsilon\Delta_{r-2})$ for $r\ge3$;
--   2. $\Delta'_r<8A(\Delta_r+\varepsilon)$ for $r=1,2$;
--   3. $\delta'<4A(\delta+\varepsilon)$.
--
--
--   The standing assumptions of §8 apply: $A$ is large ($A\ge A_0$, a power of $2$), $\varepsilon$ is small in terms of $A$ ($0<\varepsilon<\varepsilon_0$), $n$ is a power of $2$, and $\alpha=1/A$. Each $\mathrm{ns}_m$ may be any standard $\varepsilon$-nearsort network on $m$ registers.
--
--   A single nearsort step cannot increase the errors much.
--
--   Differences from the source:
--   - correction: Δ′r < 8A(Δr + εΔr−2), r ≥ 3 → Δ′r ≤ 8A(Δr + εΔr−2); reason: at the sorted input every Δ is 0 before and after the step, so the strict inequality reads 0 < 0
--   - reading: the errors before a Zig (or a Zag) step → any configuration (a permutation) at time t ≥ 1; reason: the stronger reading: the proof uses only δ < α² and the nearsort property, not the history of the run
--   - reading: α small (A large), ε sufficiently small in terms of α; α never defined → ∃ A₀, ∀ A ≥ A₀ a power of 2, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); α = 1/A; reason: the standing assumption of §8, p.7, in quantifier form; the proofs use α = 1/A (|J′| > |J|α/2 in Lemma 1, the α/4 extreme interval and 4Aδ < 1 from δ < α² in the Remark, p.8)
--   - generalization: the algorithm with the ε-nearsort of §4 → any family of standard ε-nearsort networks ns m; reason: the proof uses only the ε-nearsort property; the §4 networks are one such family
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, Lemma 2, p.8

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_RegisterAssignment
import Definitions.Def_AKSZigZag_zigzag
import Definitions.Def_AKSZigZag_Errors

namespace AKSZigZag

open AKSSorting.Core

/-- **Lemma 2** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.8), *corrected* (`≤` in the
`r ≥ 3` clause): "Let Δr and δ be the errors before a Zig (or a Zag) step, and Δ'r and δ' after
it. If δ < α², then Δ'r < 8A(Δr+εΔr-2) r ≥ 3, Δ'r < 8A(Δr+ε) r = 1,2, δ' < 4A(δ+ε)".

For `1 ≤ t ≤ log₂ n`, any configuration `y` (a permutation) with `δ < α²`, and `y'` the
configuration after one Zig step (`zigNet`, the parts of `P_t1`) or one Zag step (`zagNet`,
`P_t2`) of cycle `t`:
1. `Δ'_r ≤ 8A(Δ_r + εΔ_{r-2})` for `r ≥ 3`;
2. `Δ'_r < 8A(Δ_r + ε)` for `r = 1, 2`;
3. `δ' < 4A(δ + ε)`.

**Formalization Note.** The standing assumptions of §8, p.7 ("we will assume that α is
small (A is large), and ε is sufficiently small in terms of α") are `∃ A₀, ∀ A ≥ A₀` and
`∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`, with `α = 1/A` (α is never defined; the proofs use `α = 1/A`). `A`
and `n` are powers of 2 (§5). `ns m` is any standard ε-nearsort network on `m` registers. The
errors `Δ_r`, `δ` at time `t` are `Delta A n t r`, `delta A n t`, computed for a configuration
`y : Fin n → Fin n` (register ↦ content) with the intervals of time `t`.
The lemma is stated for every configuration, not only those reached by the algorithm. The strict
`<` of clause 1 is false at the sorted input (both sides `0`) and is corrected to `≤`. -/
theorem lemma_2 :
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → (∃ k, A = 2 ^ k) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ n : ℕ, (∃ k, n = 2 ^ k) →
    ∀ ns : (m : ℕ) → ComparatorNetwork m, (∀ m, IsStandard (ns m) ∧ IsNearsort ε (ns m)) →
    ∀ t : ℕ, 1 ≤ t → t ≤ Nat.log 2 n →
    ∀ y : Fin n → Fin n, Function.Bijective y →
    delta A n t y < (1 / (A : ℝ)) ^ 2 →
    ∀ N ∈ [zigNet A ns n t, zagNet A ns n t],
      (∀ r : ℕ, 3 ≤ r →
        Delta A n t r (N.eval y) ≤ 8 * A * (Delta A n t r y + ε * Delta A n t (r - 2) y)) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 2 → Delta A n t r (N.eval y) < 8 * A * (Delta A n t r y + ε)) ∧
      delta A n t (N.eval y) < 4 * A * (delta A n t y + ε) := by sorry

end AKSZigZag
