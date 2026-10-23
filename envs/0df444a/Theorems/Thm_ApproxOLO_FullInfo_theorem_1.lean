-- Prove2me | Theorems.Thm_ApproxOLO_FullInfo_theorem_1
-- name    : ApproxOLO.FullInfo.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:36.343717+00:00
-- url     : https://prove2.me/theorems/3123ca0d-17a2-4d1b-bfe3-981f8e300431
-- title:
--   Theorem 1, p. 14 — Algorithm 3 has expected α-regret at most α²R²/(Tη) + ηF²/2 + 3Fε
-- statement:
--   There is a universal constant $c>0$ (the constant of Lemma 5, fixing the number of Ellipsoid iterations in every call of Algorithm 2) such that the following holds. Let $d\ge2$, let $\mathcal K,\mathcal F\subset\mathbb R^d_+$, $R,F,C$ be an instance of online linear optimization, $\mathcal O_{\mathcal K}$ an $\alpha$-approximation oracle for some $\alpha>0$, $\eta>0$, $\varepsilon\in(0,(\alpha+2)R]$, $T\ge1$, and let $f_1,\dots,f_T\in\mathcal F$ be loss/payoff vectors fixed in advance (oblivious adversary). Run Algorithm 3 (online gradient descent with infeasible projections onto $\mathrm{CH}(\alpha\mathcal K)$) for $T$ rounds, and let $s_1,\dots,s_T$ be the points it plays. Then
--   $$\mathbb E\big[\alpha\text{-regret}(\{(s_t,f_t)\}_{t\in[T]})\big]\le\frac{\alpha^2R^2}{T\eta}+\frac{\eta F^2}{2}+3F\varepsilon .$$
--
--   This holds in both regimes: $\alpha\ge1$ (losses, regret against $\alpha$ times the best fixed point of $\mathcal K$) and $\alpha<1$ (payoffs). With $\eta$ and $\varepsilon$ tuned in $T$ it gives vanishing expected $\alpha$-regret using only the approximation oracle.
--
--   **Formalization Note** The expected $\alpha$-regret is Eq. (1) evaluated at the expected per-round losses/payoffs $\mathbb E[s_t\cdot f_t]$: $s_1\cdot f_1$ in round 1 and $\sum_ia_i\,s_i\cdot f_t$ for $t\ge2$, with the distribution and points returned by the call of round $t-1$. This equals the expectation of (1) by linearity, because the iterates $\tilde y_t$ and the distributions never depend on the sampled points and the losses are fixed in advance; no probability space is built. A run of Algorithm 3 is a run predicate: $s_1\in\mathcal K$ is arbitrary and every call of rounds $1,\dots,T-1$ is a complete run of Algorithm 2 (the call of round $T$ only produces $s_{T+1}$). Added hypotheses: $d\ge2$ (the central-cut update), $T\ge1$ (the factor $1/T$). The oracle-complexity bound $K(\eta,\varepsilon)$ and the two "In particular" settings of the theorem are not stated: they are $O(\cdot)$ bounds with hidden constants. $\|\cdot\|$ is Euclidean.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, p. 14, Theorem 1 (regret bound; Algorithm 3, proof pp. 14–15)

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

namespace ApproxOLO.FullInfo

open Matrix

/-- **Theorem 1 (Main Theorem), Garber, arXiv:1709.03093v1, p. 14 (regret bound).** There is a
universal constant `c > 0` (the constant of Lemma 5 fixing the Ellipsoid iterations in every
call of Algorithm 2) such that for every `d ≥ 2`, instance, `α > 0`, oracle, `η > 0`,
`ε ∈ (0, (α + 2)R]`, `T ≥ 1` and loss/payoff vectors `f_1, …, f_T ∈ F`, every run of
Algorithm 3 satisfies `E[α-regret({(s_t, f_t)}_{t∈[T]})] ≤ α²R²/(Tη) + ηF²/2 + 3Fε`,
where the expected `α`-regret is (1) evaluated at the expected per-round losses/payoffs
`E[s_t · f_t]`. -/
theorem theorem_1 : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
    ∀ (K Fs : Set (Vec d)) (R Fb C alpha eta eps : ℝ) (O : Vec d → Vec d) (T : ℕ)
      (fs : ℕ → Vec d) (s1 : Vec d) (outs : ℕ → Alg2Out d),
    IsInstance K Fs R Fb C → 0 < alpha → IsApproxOracle K alpha O →
    0 < eta → 0 < eps → eps ≤ (alpha + 2) * R → 1 ≤ T →
    (∀ t ∈ Finset.Icc 1 T, fs t ∈ Fs) →
    IsAlg3Run c K O alpha R eta eps T fs s1 outs →
    regretOf K alpha T fs (alg3ExpLoss s1 outs fs)
      ≤ alpha ^ 2 * R ^ 2 / (T * eta) + eta * Fb ^ 2 / 2 + 3 * Fb * eps := by sorry

end ApproxOLO.FullInfo
