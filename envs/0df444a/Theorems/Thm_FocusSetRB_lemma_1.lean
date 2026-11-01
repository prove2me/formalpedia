-- Prove2me | Theorems.Thm_FocusSetRB_lemma_1
-- name    : FocusSetRB.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:09.288049+00:00
-- url     : https://prove2.me/theorems/028165ab-5f5c-4c86-bcce-1572389833f7
-- title:
--   Lemma 1, eq. (31), p.17 — pseudo-contraction of $P_{\bar\pi^*}$ in $\|\cdot\|_W$
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1). For every probability distribution $v$ on $\mathbb S$, viewed as a row vector,
--
--   $$
--   \|v P_{\bar\pi^*}-\mu^*\|_W\le\Big(1-\frac{1}{2\lambda_W}\Big)\|v-\mu^*\|_W ,
--   $$
--
--   where $W$ is the matrix of Definition 2, $\lambda_W$ its maximal eigenvalue and $\|u\|_W=\sqrt{uWu^\top}$.
--
--   One step of the single-armed chain brings any distribution geometrically closer to $\mu^*$ in the $W$-norm; this is the drift behind the subset Lyapunov functions $h_W$.
--
--   Differences from the source:
--   - encoding: distribution v ∈ Δ(𝕊), row vectors → v : S → ℝ nonnegative with ∑ v = 1; vP written v ᵥ* P; reason: Lean convention
--   - encoding: λ_W the maximal eigenvalue of W → λ_W the maximal Rayleigh quotient sup over ‖u‖₂ = 1 of u W uᵀ; reason: equal for the symmetric matrix W
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - encoding: W = ∑_{k≥0} (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k → a tsum in Matrix S S ℝ with the entrywise topology; reason: the series converges under Assumption 1 (Lemma 11), so the tsum is its sum
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 1, eq. (31), p.17

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_W

namespace FocusSetRB

open Matrix

/-- **Lemma 1 (Pseudo-contraction under `W`-weighted `L₂` norm), eq. (31), p.17** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4).
Suppose `P_π̄*` is an aperiodic unichain on `𝕊`. Then for any distribution `v ∈ Δ(𝕊)`,
`‖v P_π̄* − μ*‖_W ≤ (1 − 1/(2λ_W)) ‖v − μ*‖_W`, where `λ_W` is the maximal eigenvalue of `W`
(Definition 2) and `‖u‖_W = √(u W uᵀ)`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** Distributions are nonnegative `v : S → ℝ` summing to one, treated as row
vectors (`v ᵥ* P` is `vP`). -/
theorem lemma_1 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    (v : S → ℝ) (hv0 : ∀ s, 0 ≤ v s) (hv1 : ∑ s, v s = 1) :
    normW M y (v ᵥ* Ppi M y - muStar y) ≤
      (1 - 1 / (2 * lamW M y)) * normW M y (v - muStar y) := by sorry

end FocusSetRB
