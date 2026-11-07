-- Prove2me | Theorems.Thm_CtxSearchTSR_theorem_2_4_adversarial_contextual_search
-- name    : CtxSearchTSR.theorem_2_4_adversarial_contextual_search
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:20.569719+00:00
-- url     : https://prove2.me/theorems/f5217a64-1afd-4fa1-bac4-8bc55a8d3f1a
-- title:
--   Theorem 2.4 — Algorithm 2 has expected total loss $\sum_{t=1}^T\mathbb E[\ell_t]\le12\sqrt d$ against every adaptive context strategy
-- statement:
--   Let $d\in\mathbb N$, let $z\in\mathbb R^d$ be a fixed target with $\|z\|_2\le1$, and let the contexts $x_1,x_2,\dots$ be chosen by an adaptive strategy: $x_t$ may depend on everything observed before round $t$ (past contexts, prices, feedback and the learner's past random signs) but not on the learner's fresh sign $\varepsilon_t$, and $\|x_t\|_2\le1$ for all $t$. Then for every horizon $T$, Algorithm 2 satisfies
--
--   $$\sum_{t=1}^T\mathbb E[\ell_t]\le12\sqrt d, \tag{11}$$
--
--   where $\ell_t=|x_t^\top z-P_t|$ is the loss of the posted price $P_t$ and the expectation is over the learner's independent uniform signs.
--
--   The bound does not depend on $T$: the learner suffers bounded total loss in the worst case over targets and adaptive contexts, using one-bit feedback only. The algorithm uses $O(d^2)$ arithmetic operations and $O(d^2)$ real-valued storage per round.
--
--   **Formalization Note** A context strategy is a map from the learner's previous signs to the next context; for a fixed target this determines the whole history. The expectation is the average over the $2^T$ sign vectors. The Euclidean norm is written out as $\sqrt{v^\top v}$.
--
--   Differences from the source:
--   - generalization: every horizon T ≥ 1 (and d ≥ 1 implicit) → every T ∈ ℕ and every d ∈ ℕ; reason: at T = 0 the sum is empty and at d = 0 every price and loss is 0, so both bounds read 0 ≤ 12√d; it specializes to the paper's T ≥ 1, d ≥ 1
--   - reading: "every admissible adaptive context strategy" (contexts adapt to the history, chosen before the learner's fresh randomization) → a deterministic map from the learner's previous signs to the next context; reason: for a fixed target the history is a function of the past signs; a strategy with its own randomness independent of the learner's is a mixture of deterministic ones, and the bound passes to it by averaging
--   - encoding: 𝔼 over the learner's i.i.d. uniform signs → the average over the 2^T sign vectors Fin T → Bool; reason: the signs are the only randomness; by linearity Σ_t 𝔼[ℓ_t] = 𝔼[Σ_t ℓ_t]
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean indexing; same rounds
--   - encoding: the update (10) at x_t = 0 (a_t = 0, the division in (10) is undefined; the paper says the loss and potential change are both zero, App. C.3, p.21) → Lean's c/0 = 0 makes the update the identity and the price x⊤m + 0 = 0; reason: the paper's own convention for x_t = 0; no instance changes
--   - reading: "The algorithm uses O(d2) arithmetic operations and O(d2) real-valued storage per round" → not a separate Lean clause; the state type is (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ (d + d² reals) and the update is the closed form (10) (one matrix–vector product, one rank-one update); reason: the paper defines no cost model, and Lean's real arithmetic has none
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2.2, Theorem 2.4, p.10, (11), with its last sentence on p.11

import Mathlib
import Definitions.Def_CtxSearchTSR_ExpectedTotalLoss

open Matrix

namespace CtxSearchTSR

/-- **Theorem 2.4 (Adversarial Contextual Search).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), p.10, (11), with its last sentence on
p.11.

"For every fixed z with ‖z‖₂ ≤ 1, every horizon T ≥ 1, and every admissible adaptive context
strategy with ‖x_t‖₂ ≤ 1, Algorithm 2 satisfies Σ_{t=1}^T 𝔼[ℓ_t] ≤ 12√d." (11)

**Formalization Note.** Contexts are chosen by a non-anticipating strategy `X` (round t's context is
a function of the learner's previous signs, never of the current one), and every context lies in
the Euclidean unit ball. The expectation is over the learner's i.i.d. uniform signs
(`expectedTotalLoss`). T = 0 is allowed (the sum is empty). The sentence "The algorithm uses O(d²)
arithmetic operations and O(d²) real-valued storage per round" has no Lean clause: the state is
(**m**, R) ∈ ℝ^d × ℝ^{d×d} and the update is the closed form (10). -/
theorem theorem_2_4_adversarial_contextual_search {d : ℕ} (z : Fin d → ℝ) (hz : eucNorm z ≤ 1)
    (X : ContextStrategy d) (hX : ∀ (t : ℕ) (h : Fin t → Bool), eucNorm (X t h) ≤ 1) (T : ℕ) :
    expectedTotalLoss z X T ≤ 12 * Real.sqrt d := by sorry

end CtxSearchTSR
