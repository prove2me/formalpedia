-- Prove2me | Theorems.Thm_FocusSetRB_lemma_2
-- name    : FocusSetRB.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:58.36006+00:00
-- url     : https://prove2.me/theorems/fbf447d7-aab6-4522-a993-fca031d99560
-- title:
--   Lemma 2, eqs. (33)–(35), p.18 — $h_W$ are subset Lyapunov functions
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $N\ge1$, and let $h_W(x,D)=\|x(D)-m(D)\mu^*\|_W$. For every system state $x$ and all $D\subseteq D'\subseteq[N]$:
--
--   1. (33) if the arms of $D$ take actions $A_0(i)\sim\bar\pi^*(\cdot\mid x(i))$ (the other arms taking any actions),
--   $$
--   \mathbb E\big[h_W(X_1,D)\mid X_0=x\big]\le\Big(1-\frac1{2\lambda_W}\Big)h_W(x,D)+\frac{2\lambda_W^{1/2}}{\sqrt N};
--   $$
--   2. (34) $h_W(x,D)\ge|\mathbb S|^{-1/2}\,\|x(D)-m(D)\mu^*\|_1$;
--   3. (35) $|h_W(x,D)-h_W(x,D')|\le 2\lambda_W^{1/2}\big(m(D')-m(D)\big)$.
--   4. Consequently $\{h_W(\cdot,D)\}_{D\subseteq[N]}$ is a class of subset Lyapunov functions for $\bar\pi^*$ (Definition 1), with $\rho_2=1-1/(2\lambda_W)$, $K_{\mathrm{drift}}=2\lambda_W^{1/2}$, $K_{\mathrm{dist}}=|\mathbb S|^{-1/2}$ and $L_h=2\lambda_W^{1/2}$.
--
--   Differences from the source:
--   - encoding: A₀(i) ∼ π̄*(·|S₀(i)) for i ∈ D, the actions of the other arms unspecified → the other arms take arbitrary actions aOut, quantified over every choice; reason: the quantity depends only on the arms of D, whose next states depend only on their own actions, so every law of the other actions gives the same expectation
--   - encoding: λ_W the maximal eigenvalue of W → λ_W the maximal Rayleigh quotient sup over ‖u‖₂ = 1 of u W uᵀ; reason: equal for the symmetric matrix W
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - encoding: W = ∑_{k≥0} (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k → a tsum in Matrix S S ℝ with the entrywise topology; reason: the series converges under Assumption 1 (Lemma 11), so the tsum is its sum
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 2, eqs. (33)–(35), p.18

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_scaledCount
import Definitions.Def_FocusSetRB_IsSubsetLyapunov

namespace FocusSetRB

/-- **Lemma 2, eqs. (33)–(35), p.18** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4). The functions
`h_W(x, D) = ‖x(D) − m(D)μ*‖_W`, `D ⊆ [N]`, satisfy, for every system state `x` and every pair
`D ⊆ D' ⊆ [N]`:
* (33) `𝔼[h_W(X₁, D) | X₀ = x, A₀(i) ∼ π̄*(·|S₀(i)) ∀ i ∈ D] ≤ (1 − 1/(2λ_W)) h_W(x, D) +
  2λ_W^{1/2}/√N`;
* (34) `h_W(x, D) ≥ |𝕊|^{−1/2} ‖x(D) − m(D)μ*‖₁`;
* (35) `|h_W(x, D) − h_W(x, D')| ≤ L_W (m(D') − m(D))` with `L_W = 2λ_W^{1/2}`.
Consequently `{h_W(·, D)}_{D ⊆ [N]}` is a class of subset Lyapunov functions for `π̄*` (Definition 1),
with `ρ₂ = 1 − 1/(2λ_W)`, `K_drift = 2λ_W^{1/2}`, `K_dist = |𝕊|^{−1/2}` and `L_h = L_W`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** Arms are `Fin N`, `N ≥ 1`. In (33) the arms of `D` take their ideal
actions `Â(i) ∼ π̄*(·|x(i))` and the arms outside `D` take arbitrary actions `aOut`, quantified
universally (`h_W(·, D)` does not see them); the expectation is over `Â` and the next state. -/
theorem lemma_2 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N : ℕ} (hN : 1 ≤ N) (x : Fin N → S) (D D' : Finset (Fin N)) (hDD' : D ⊆ D') :
    (∀ aOut : Fin N → Bool,
      ∑ Ahat, idealLaw y x Ahat *
          ∑ x', stepProb M x (followOn D Ahat aOut) x' * hW M y x' D ≤
        (1 - 1 / (2 * lamW M y)) * hW M y x D + 2 * Real.sqrt (lamW M y) / Real.sqrt N) ∧
    1 / Real.sqrt (Fintype.card S) * l1Dev y x D ≤ hW M y x D ∧
    |hW M y x D - hW M y x D'| ≤ 2 * Real.sqrt (lamW M y) * (frac D' - frac D) ∧
    IsSubsetLyapunov (N := N) M y Set.univ (hW M y) (1 - 1 / (2 * lamW M y)) (2 * Real.sqrt (lamW M y))
      (1 / Real.sqrt (Fintype.card S)) (2 * Real.sqrt (lamW M y)) := by sorry

end FocusSetRB
