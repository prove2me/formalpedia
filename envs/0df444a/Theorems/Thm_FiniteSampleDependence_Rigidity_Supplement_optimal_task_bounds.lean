-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_optimal_task_bounds
-- name    : FiniteSampleDependence.Rigidity.Supplement.optimal_task_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:51:43.546247+00:00
-- url     : https://prove2.me/theorems/ddd29b91-d2b9-4253-a671-c351f6085c04
-- title:
--   Theorem 6.2 — optimal task bounds: $F_A\equiv0$ for $n>m$, no doubly nontrivial dominantly truthful mechanism for $n\ne m$, and $\ell\ge2n$ tasks, attained, for $n=m$
-- statement:
--   Let $n,m\ge2$ and consider $\ell$-task peer-prediction mechanisms $(M_A,M_B)$, $M_A,M_B:([n]\times[m])^\ell\to\mathbb R$, with independence-zero expected payments, in the memoryless strategy model of §6 (reports i.i.d. from $TPS^\top$ for column-stochastic channels $T$ of Alice and $S$ of Bob).
--
--   1. **(i), tall case.** If $n>m$, then for every $\ell\in\mathbb N$ and every independence-zero payment $M_A$ that is truthful for Alice against all memoryless deviations with Bob truthful,
--   $$F_A(U)=\mathbb E_{U^{\otimes\ell}}[M_A]=0\qquad\text{for every }U\in\Delta_{n,m}.$$
--   2. **(i), consequence.** If $n\ne m$, then for every $\ell$ no dominantly truthful mechanism $(M_A,M_B)$ with independence-zero payments has nontrivial expected payments for both agents.
--   3. **(ii), lower bound.** If $n=m$, every independence-zero payment $M_A$ on $\ell$ tasks that is truthful for Alice against all memoryless deviations with Bob truthful and has nontrivial Alice payment satisfies $\ell\ge2n$.
--   4. **(ii), attainment.** If $n=m$, there is a $2n$-task mechanism $(M_A,M_B)$ with independence-zero payments that is dominantly truthful in the memoryless strategy model and has nontrivial expected payments for both agents.
--
--   Here *nontrivial* means the truthful expected payment is nonzero for at least one $P\in\Delta_{n,m}$, and *dominantly truthful* means that against every fixed column-stochastic channel of the other agent, truthful reporting maximizes one's expected payment over all own column-stochastic channels. The bound $2n$ is exact; it is the degree bound of the mission's goal translated into a task count.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: the i.i.d. expectation E_{V^{⊗ℓ}}[M] of a payment rule → the exact finite sum Σ_{z ∈ ([n]×[m])^ℓ} M(z) ∏_t V_{x_t y_t} (expectedPayment), the paper's equation (6); reason: for finitely many outcomes the expectation is this sum; no measure-theoretic model is introduced
--   - encoding: a mechanism (M_A, M_B) with independence-zero expected payments, in clauses (i) first sentence and (ii) first sentence → quantification over Alice's payment M_A alone, with PaymentIZ M_A; reason: Bob's payment does not enter these clauses; every such M_A is the Alice payment of a mechanism with M_B = 0, which is independence-zero
--   - encoding: F_A ≡ 0 → expectedPayment M_A U = 0 for every U ∈ Δ_{n,m}; reason: F_A is a functional on the simplex
--   - encoding: every finite-task mechanism; for unequal alphabet sizes → every ℓ : ℕ (ℓ = 0 included); n ≠ m; reason: a finite number of tasks is a natural number
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem 6.2, PDF p. 17 (printed p. 16); proof PDF pp. 17–18 (printed pp. 16–17); model of §6, PDF p. 17

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Theorem 6.2 (Optimal task bounds), PDF p. 17 (printed p. 16), for mechanisms with
independence-zero expected payments in the memoryless strategy model of §6.
(i) If `n > m`, every finite-task mechanism truthful for Alice against all memoryless deviations
with Bob truthful has `F_A ≡ 0`; consequently, for `n ≠ m`, no finite-task dominantly truthful
mechanism has nontrivial expected payments for both agents.
(ii) If `n = m`, every such Alice-truthful mechanism with nontrivial Alice payment has
`ℓ ≥ 2n` tasks, and some `2n`-task mechanism is dominantly truthful with nontrivial payments for
both agents. -/
theorem optimal_task_bounds {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    -- (i), first sentence
    (m < n → ∀ (ℓ : ℕ) (MA : (Fin ℓ → Fin n × Fin m) → ℝ), PaymentIZ MA → AliceTruthful MA →
      ∀ U ∈ simplex n m, expectedPayment MA U = 0) ∧
    -- (i), second sentence
    (n ≠ m → ∀ (ℓ : ℕ) (MA MB : (Fin ℓ → Fin n × Fin m) → ℝ),
      PaymentIZ MA → PaymentIZ MB → DominantlyTruthful MA MB →
        ¬ (PaymentNontrivial MA ∧ PaymentNontrivial MB)) ∧
    -- (ii), lower bound
    (n = m → ∀ (ℓ : ℕ) (MA : (Fin ℓ → Fin n × Fin m) → ℝ), PaymentIZ MA → AliceTruthful MA →
      PaymentNontrivial MA → 2 * n ≤ ℓ) ∧
    -- (ii), attainment
    (n = m → ∃ MA MB : (Fin (2 * n) → Fin n × Fin m) → ℝ,
      PaymentIZ MA ∧ PaymentIZ MB ∧ DominantlyTruthful MA MB ∧
        PaymentNontrivial MA ∧ PaymentNontrivial MB) := by sorry

end FiniteSampleDependence.Rigidity.Supplement
