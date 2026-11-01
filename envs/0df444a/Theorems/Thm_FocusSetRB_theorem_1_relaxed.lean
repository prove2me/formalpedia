-- Prove2me | Theorems.Thm_FocusSetRB_theorem_1_relaxed
-- name    : FocusSetRB.theorem_1_relaxed
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:36.571989+00:00
-- url     : https://prove2.me/theorems/1c9273d9-9538-4c58-9400-70e97805657c
-- title:
--   Proof of Theorem 1, display, p.18 — $R^{\mathrm{rel}}-R(\pi,S_0)\le 256\,r_{\max}\lambda_W^2|\mathbb S|^2/(\beta^2\sqrt N)$
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $0<\alpha<1$, $\beta=\min\{\alpha,1-\alpha\}$, $N\ge1$ and $k=\alpha N\in\mathbb N$, and let $\lambda_W$ be the maximal eigenvalue of the matrix $W$ of Definition 2. Let $\pi$ be the set-expansion policy: a focus-set policy started from the initial focus set $D_{-1}=\emptyset$ whose update obeys Algorithm 2, lines 2–5, and whose rectifier obeys Algorithm 1's (4)–(5). Then for every initial state vector $S_0$,
--
--   $$
--   R^{\mathrm{rel}}-R^-(\pi,S_0)\le\frac{256\,r_{\max}\,\lambda_W^2\,|\mathbb S|^2}{\beta^2\sqrt N}
--   $$
--
--   This is the display that closes the proof of Theorem 1: Lemmas 3, 4 and 5 verify Conditions 1–3 for the subset Lyapunov functions $h_W$ of Lemma 2, and Theorem 5 is applied with the resulting constants, every $1/N$ being relaxed to $1/\sqrt N$.
--
--   Differences from the source:
--   - reading: R(π, S₀), the long-run average reward → R⁻(π, S₀), the liminf average reward; reason: p.5 defines the optimality gap as R*(N,S₀) − R⁻(π,S₀) and writes R(π,S₀) for it when the limit exists; R⁻ is always defined and equals R where the limit exists
--   - generalization: the set-expansion policy of Algorithm 2 ("any set with the largest m(D_t)", uniform tie-breaking in lines 6–15) → every update kernel whose possible outputs obey lines 2–5 and every rectifier kernel whose possible outputs obey Algorithm 1's (4)–(5); reason: contains Algorithm 2 with every choice of maximizer and its uniform tie-breaking; p.10 says the analysis holds whenever lines 4–5 of Algorithm 1 are satisfied
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: λ_W the maximal eigenvalue of W → λ_W the maximal Rayleigh quotient sup over ‖u‖₂ = 1 of u W uᵀ; reason: equal for the symmetric matrix W
--   - encoding: αN an integer, N arms → k : ℕ with (k : ℝ) = α·N and N ≥ 1; reason: the paper assumes αN is an integer (p.5); an N-armed problem has N ≥ 1
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - encoding: W = ∑_{k≥0} (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k → a tsum in Matrix S S ℝ with the entrywise topology; reason: the series converges under Assumption 1 (Lemma 11), so the tsum is its sum
--   - reading: D_t chosen based on X_t and D_{t−1}, actions based on X_t and D_t (Algorithm 1), "any set" in Algorithm 2 → the update and the rectifier are fixed kernels that do not depend on t; reason: Algorithm 1 names those as the inputs of the rule, and Appendix D (p.40) treats (S_t, A_t, X_t, D_t) as a finite-state Markov chain
--   - encoding: R^rel the optimal value of (LP) → the real sSup of the (LP) objective over the feasible set; reason: for 0 < α < 1 the feasible set is nonempty and compact, so the supremum is the maximum
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, proof of Theorem 1, display, p.18

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_IsSetExpansionSelector

namespace FocusSetRB

/-- **Proof of Theorem 1, display, p.18** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4). For the set-expansion policy `π`
(Algorithm 2, initial focus set `D_{−1} = ∅`), by Lemmas 3, 4, 5 and Theorem 5,
`R^rel − R(π, S₀) ≤ 256 r_max λ_W² |𝕊|² / (β² √N)`, `β = min{α, 1 − α}`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** `R(π, S₀)` is the liminf average reward `R⁻(π, S₀)` of the focus-set
process. The set-expansion policy is any focus-set process whose update kernel obeys
Algorithm 2's lines 2–5 and whose rectifier obeys Algorithm 1's (4)–(5); Algorithm 2's
lines 6–15 are one such rectifier (p.10). Arms are `Fin N`, `N ≥ 1`, `k = αN`; `λ_W` is the
maximal eigenvalue of `W` (Definition 2). -/
theorem theorem_1_relaxed {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N k : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) = α * N)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (hsel : IsSetExpansionSelector α y sel)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (hrect : IsRectifier k rect)
    (S0 : Fin N → S) :
    Rrel M α - focusRminus M y sel rect S0 ∅ ≤
      256 * rmax M * lamW M y ^ 2 * (Fintype.card S : ℝ) ^ 2 / (beta α ^ 2 * Real.sqrt N) := by sorry

end FocusSetRB
