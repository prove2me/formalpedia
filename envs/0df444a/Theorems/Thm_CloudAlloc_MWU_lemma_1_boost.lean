-- Prove2me | Theorems.Thm_CloudAlloc_MWU_lemma_1_boost
-- name    : CloudAlloc.MWU.lemma_1_boost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:40:11.43227+00:00
-- url     : https://prove2.me/theorems/ff0d8e5e-b483-4ac3-8815-41bc44472377
-- title:
--   Lemma 1: multiplicative boost of active users
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs $\beta(i)\ge 0$ with $\sum_i\beta(i)\le 1$, and nonnegative loads. Let $h$ be a run of Algorithm 1, $A_t$ the active users at time $t$, $A^1_t=\{i\in A_t: h_t(i)<\beta(i)\}$, $A^2_t=A_t\setminus A^1_t$, and $c=\varepsilon\eta/(4N)$. Then:
--
--   1. if $\sum_{j\in A_t}h_t(j)\le 1-\varepsilon$, every $i\in A_t$ satisfies $h_{t+1}(i)\ge h_t(i)(1+c)$;
--   2. every $i\in A^1_t$ satisfies $h_{t+1}(i)\ge h_t(i)$;
--   3. every $i\in A^2_t$ satisfies $h_{t+1}(i)\ge h_t(i)(1-\varepsilon c)$.
--
--   When the system is under-utilized all active users gain multiplicatively, and in general active users lose little. This drives the utilization bound of Claim 3.2 and the SLA argument of Theorem 4.
--
--   Differences from the source:
--   - generalization: η in Algorithm 1's input range 0 < η < 1/3 (no η range printed in this statement) → 0 < η ≤ 1/3; reason: the range printed in Lemma 2 and Theorem 4; it contains Algorithm 1's input range, so the statement specializes to it
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Lemma 1, p. 11 (proof in Appendix B, pp. 27–29)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run

namespace CloudAlloc.MWU

/-- **Lemma 1: multiplicative boost of active users.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Lemma 1, p. 11 (proof in Appendix B, pp. 27–29):
"Let `c = εη/(4N)`. Then Algorithm 1 satisfies the following:
1. Suppose `Σ_{i∈At} ht(i) ≤ 1 − ε`. If `i ∈ At`, then `ht+1(i) ≥ ht(i)(1 + c)`.
2. In general, Algorithm 1 satisfies `ht+1(i) ≥ ht(i)` for `i ∈ A¹t` and `ht+1(i) ≥ ht(i)(1 − εc)`
for `i ∈ A²t`."

For every run `h` of Algorithm 1 with `N ≥ 2`, `0 < ε ≤ 1/10`, `0 < η ≤ 1/3`, SLAs `β ≥ 0` with
`Σβ ≤ 1` and nonnegative loads, and with `c = εη/(4N)`:
(1) if the active users hold at most `1 − ε` in total, every active user's allocation grows by the
factor `1 + c`; (2) an active user below its SLA does not lose allocation; (3) an active user at or
above its SLA keeps at least the fraction `1 − εc` of its allocation.

**Formalization Note.** Lean time `t` is the paper's `t + 1` (`h t` = `h_{t+1}`,
`queue h L t` = `Q_{t+1}`). Active means `0 < queue h L t i` (`A_t`); `A¹_t` is `h t i < β i`, `A²_t`
is `β i ≤ h t i`. The η range `0 < η ≤ 1/3` is that of Lemma 2 and Theorem 4 (p. 10, 13); Lemma 1
prints no η range, and `0 < η` comes from Algorithm 1's input (p. 9). -/
theorem lemma_1_boost {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let c := ε * η / (4 * (N : ℝ))
    (∀ t, ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L t j), h t j ≤ 1 - ε →
        ∀ i, 0 < queue h L t i → h t i * (1 + c) ≤ h (t + 1) i) ∧
      (∀ t i, 0 < queue h L t i → h t i < β i → h t i ≤ h (t + 1) i) ∧
      (∀ t i, 0 < queue h L t i → β i ≤ h t i → h t i * (1 - ε * c) ≤ h (t + 1) i) := by sorry

end CloudAlloc.MWU
