-- Prove2me | Theorems.Thm_AKSZigZag_lemma_3
-- name    : AKSZigZag.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:54.383452+00:00
-- url     : https://prove2.me/theorems/e4fa47d4-62e0-4d30-aabd-ef5e740106af
-- title:
--   Lemma 3, p.8 — a ZigZag step: $\Delta'_r\le64A^2(\Delta_{r+1}+3\varepsilon\Delta_{r-4})$ (corrected: $\le$ for $r\ge5$)
-- statement:
--   Let $1\le t\le\log_2 n$, and let $y$ be any configuration (a permutation) whose error $\delta$ with the intervals of time $t$ satisfies $\delta<\alpha^4$. Let $y'$ be the configuration after one Zig step followed by one Zag step of cycle $t$. Then:
--   1. $\Delta'_r\le64A^2(\Delta_{r+1}+3\varepsilon\Delta_{r-4})$ for $r\ge5$;
--   2. $\Delta'_r<64A^2(\Delta_{r+1}+3\varepsilon)$ for $r=1,2,3,4$;
--   3. $\delta'<16A^2(\delta+2\varepsilon)$.
--
--
--   The standing assumptions of §8 apply: $A$ is large ($A\ge A_0$, a power of $2$), $\varepsilon$ is small in terms of $A$ ($0<\varepsilon<\varepsilon_0$), $n$ is a power of $2$, and $\alpha=1/A$. Each $\mathrm{ns}_m$ may be any standard $\varepsilon$-nearsort network on $m$ registers.
--
--   A full ZigZag shifts the error profile by one level ($\Delta_{r+1}$ on the right), which, iterated, makes the errors decay.
--
--   Differences from the source:
--   - correction: Δ′r < 64A²(Δr+1 + 3εΔr−4), r ≥ 5 → Δ′r ≤ 64A²(Δr+1 + 3εΔr−4); reason: at the sorted input every Δ is 0 before and after the step, so the strict inequality reads 0 < 0
--   - reading: a ZigZag step of the algorithm → any configuration (a permutation) at time t ≥ 1; reason: the stronger reading: the proof uses only δ < α⁴ and the nearsort property
--   - reading: α small (A large), ε sufficiently small in terms of α; α never defined → ∃ A₀, ∀ A ≥ A₀ a power of 2, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); α = 1/A; reason: the standing assumption of §8, p.7, in quantifier form; the proofs use α = 1/A (|J′| > |J|α/2 in Lemma 1, the α/4 extreme interval and 4Aδ < 1 from δ < α² in the Remark, p.8)
--   - generalization: the algorithm with the ε-nearsort of §4 → any family of standard ε-nearsort networks ns m; reason: the proof uses only the ε-nearsort property; the §4 networks are one such family
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §8, Lemma 3, p.8

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_RegisterAssignment
import Definitions.Def_AKSZigZag_zigzag
import Definitions.Def_AKSZigZag_Errors

namespace AKSZigZag

open AKSSorting.Core

/-- **Lemma 3** (AKS, STOC 1983, doi:10.1145/800061.808726, §8, p.8), *corrected* (`≤` in the
`r ≥ 5` clause): "If δ < α⁴, then a ZigZag step will change the errors as follows
Δ'r < 64A²(Δr+1+3εΔr-4) r ≥ 5, Δ'r < 64A²(Δr+1+3ε) r = 1,2,3,4, δ' < 16A²(δ+2ε)".

For `1 ≤ t ≤ log₂ n`, any configuration `y` (a permutation) with `δ < α⁴`, and `y'` the
configuration after one Zig step followed by one Zag step of cycle `t`:
1. `Δ'_r ≤ 64A²(Δ_{r+1} + 3εΔ_{r-4})` for `r ≥ 5`;
2. `Δ'_r < 64A²(Δ_{r+1} + 3ε)` for `r = 1, 2, 3, 4`;
3. `δ' < 16A²(δ + 2ε)`.

**Formalization Note.** The standing assumptions of §8, p.7 ("we will assume that α is
small (A is large), and ε is sufficiently small in terms of α") are `∃ A₀, ∀ A ≥ A₀` and
`∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`, with `α = 1/A` (α is never defined; the proofs use `α = 1/A`). `A`
and `n` are powers of 2 (§5). `ns m` is any standard ε-nearsort network on `m` registers. The
errors `Δ_r`, `δ` at time `t` are `Delta A n t r`, `delta A n t`, computed for a configuration
`y : Fin n → Fin n` (register ↦ content) with the intervals of time `t`.
The lemma is stated for every configuration, not only those reached by the algorithm. The strict
`<` of clause 1 is false at the sorted input (both sides `0`) and is corrected to `≤`. -/
theorem lemma_3 :
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → (∃ k, A = 2 ^ k) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ n : ℕ, (∃ k, n = 2 ^ k) →
    ∀ ns : (m : ℕ) → ComparatorNetwork m, (∀ m, IsStandard (ns m) ∧ IsNearsort ε (ns m)) →
    ∀ t : ℕ, 1 ≤ t → t ≤ Nat.log 2 n →
    ∀ y : Fin n → Fin n, Function.Bijective y →
    delta A n t y < (1 / (A : ℝ)) ^ 4 →
      (∀ r : ℕ, 5 ≤ r →
        Delta A n t r ((zagNet A ns n t).eval ((zigNet A ns n t).eval y)) ≤
          64 * (A : ℝ) ^ 2 * (Delta A n t (r + 1) y + 3 * ε * Delta A n t (r - 4) y)) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 4 →
        Delta A n t r ((zagNet A ns n t).eval ((zigNet A ns n t).eval y)) <
          64 * (A : ℝ) ^ 2 * (Delta A n t (r + 1) y + 3 * ε)) ∧
      delta A n t ((zagNet A ns n t).eval ((zigNet A ns n t).eval y)) <
        16 * (A : ℝ) ^ 2 * (delta A n t y + 2 * ε) := by sorry

end AKSZigZag
