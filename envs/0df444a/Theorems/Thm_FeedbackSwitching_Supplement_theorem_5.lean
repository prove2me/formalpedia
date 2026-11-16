-- Prove2me | Theorems.Thm_FeedbackSwitching_Supplement_theorem_5
-- name    : FeedbackSwitching.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:20:49.796188+00:00
-- url     : https://prove2.me/theorems/9541e4ad-eb71-4eb0-b180-3a7a37a61e60
-- title:
--   Theorem 5 — ComparisonProbing on apple tasting: $\mathrm{Reg}_T\le\frac1\kappa+3\kappa T$, and $\mathrm{Reg}_T\le2\sqrt{3T}$ at $\kappa=1/\sqrt{3T}$
-- statement:
--   Consider apple tasting: two actions, the revealing action $1$, which observes both losses, and the blind action $2$, which observes nothing. Let $\ell_1,\dots,\ell_T\in[0,1]^2$ be an oblivious loss sequence, so that the advantages $d_t=\ell_t(1)-\ell_t(2)$ form an arbitrary deterministic sequence in $[-1,1]$. Let $\mathrm{Reg}_T$ be the expected regret with switching costs of Eq. (12),
--   $$
--   \mathrm{Reg}_T=\mathbb E\Big[\sum_{t=1}^T\ell_t(I_t)+N_T\Big]-\min_{i\in\{1,2\}}\sum_{t=1}^T\ell_t(i),
--   $$
--   where $N_T$ is the number of switches and the expectation is over the learner's coins.
--
--   1. For every $\kappa\in(0,1]$, ComparisonProbing (Algorithm 5) with probe rate $\kappa$ satisfies
--   $$
--   \mathrm{Reg}_T\le\frac1\kappa+3\kappa T .
--   $$
--   2. In particular, for $T\ge1$ and $\kappa=1/\sqrt{3T}$,
--   $$
--   \mathrm{Reg}_T\le2\sqrt{3T}.
--   $$
--
--   The bound is of order $\sqrt T$ without the logarithmic factors of the general algorithm for strongly revealing graphs, and it shows on the smallest instance the accounting the general algorithm relies on: each completed probe costs at most one unit of loss more than resting.
--
--   **Formalization Note** The regret is the base mission's `regret` on the apple-tasting graph, and the first clause also asserts that the cost is integrable over the coins. The paper states the theorem on the shifted losses $(d_t,0)$; subtracting $\ell_t(2)$ from both losses of every round leaves Eq. (12) unchanged, every $d\in[-1,1]^T$ arises from losses in $[0,1]^2$ (take $\ell_t=(d_t^+,d_t^-)$), and ComparisonProbing reads only the $d_t$, so quantifying over all loss sequences is the paper's quantifier over all advantage sequences.
--
--   Differences from the source:
--   - encoding: Reg_T on the shifted losses (d_t, 0), for every d ∈ [−1,1]^T → the regret of Eq. (12) (FeedbackSwitching.regret on the apple-tasting graph) for every loss sequence ℓ ∈ [0,1]^{T×2}; reason: subtracting ℓ_t(2) from both losses leaves Eq. (12) unchanged, every d ∈ [−1,1]^T arises as ℓ_t(1) − ℓ_t(2), and the algorithm reads only d_t, so the two quantifiers range over the same instances
--   - encoding: the expectation over the coins → the Bochner integral over the coins, with a clause asserting that the integrand is integrable; reason: the paper's expectation exists (the cost is bounded by 2T); the clause rules out Lean's junk value 0 of a non-integrable integral and changes no instance
--   - encoding: actions {1, 2}, rounds 1..T, independent Bernoulli(κ) coins → actions Fin 2 (0 revealing, 1 blind), rounds 0..T−1, coins c_t = 1{ω_t < κ} with ω i.i.d. uniform on [0,1]; reason: same law of the coins for κ ∈ (0,1]; same algorithm and same instances
--   - reading: "setting κ = 1/√(3T)" (T implicit) → the second clause for every T ≥ 1; reason: κ = 1/√(3T) is defined and lies in (0,1] exactly when T ≥ 1, which the paper's "in particular" from the first clause presupposes
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Theorem 5 (Comparison probing), Appendix A.2, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_FeedbackSwitching_regret
import Definitions.Def_FeedbackSwitching_Supplement_appleTasting
import Definitions.Def_FeedbackSwitching_Supplement_comparisonProbing
open MeasureTheory

namespace FeedbackSwitching.Supplement

/-- **Theorem 5 (Comparison probing)**, App. A.2, p.44 (PDF p.46). Cesa-Bianchi, Cesari,
Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with Switching Costs: A
Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version, sha256 ded8f8bc…).

"For every deterministic sequence `d₁, …, d_T ∈ [−1, 1]` and every `κ ∈ (0, 1]`, ComparisonProbing
satisfies `Reg_T ≤ 1/κ + 3κT`. In particular, setting `κ = 1/√(3T)` yields `Reg_T ≤ 2√(3T)`."

**Formalization Note.** The regret is the base mission's `regret` (Eq. (12)) on the apple-tasting
graph, against every oblivious loss sequence `ℓ ∈ [0,1]^{T×2}`. The paper's shifted regret on the
advantages `d_t = ℓ_t(1) − ℓ_t(2)` equals it (App. A.1), every `d ∈ [−1,1]^T` arises from such
an `ℓ`, and ComparisonProbing reads only the `d_t`; so the quantifier over `ℓ` is the paper's
quantifier over `d`. The first clause also asserts that the cost is integrable over the coins.
The second clause needs `T ≥ 1` (so that `κ = 1/√(3T)` is defined and `≤ 1`). -/
theorem theorem_5 :
    (∀ (T : ℕ) (κ : ℝ), 0 < κ → κ ≤ 1 → ∀ ℓ : LossSeq 2 T,
      Integrable (fun ω =>
          pathLoss ℓ.1 (action appleTasting (comparisonProbing κ) ℓ.1 ω)
          + pathSwitches T (action appleTasting (comparisonProbing κ) ℓ.1 ω))
        (comparisonProbing κ).μ ∧
      regret appleTasting (comparisonProbing κ) ℓ.1 ≤ 1 / κ + 3 * κ * T) ∧
    (∀ T : ℕ, 1 ≤ T → ∀ ℓ : LossSeq 2 T,
      regret appleTasting (comparisonProbing (1 / Real.sqrt (3 * T))) ℓ.1
        ≤ 2 * Real.sqrt (3 * T)) := by sorry

end FeedbackSwitching.Supplement
