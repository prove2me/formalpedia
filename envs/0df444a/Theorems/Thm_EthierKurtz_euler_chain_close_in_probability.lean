-- Prove2me | Theorems.Thm_EthierKurtz_euler_chain_close_in_probability
-- name    : EthierKurtz.euler_chain_close_in_probability
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:09:23.02222+00:00
-- url     : https://prove2.me/theorems/d20b80e0-f460-4644-a07d-7185b23d85c3
-- title:
--   Heun-type Euler chain of a Brownian SDE converges in probability on the event the solution stays bounded
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion, $X$ the solution from $x_0$ of $dX=\sigma_0(X)\,dW+b_0(X)\,dt$ with continuous coefficients, and $s_1,b_1$ bounded ($S$), $L$-Lipschitz coefficients agreeing with $\sigma_0,b_0$ on the ball $|x|\le R+3$. For step sizes $h_n>0$, $h_n\to0$, and integers $j_n$ with $T=j_nh_n$, let $Y_n$ be the Heun-type two-step Euler chain with step $h_n$ started at $(x_0,x_0)$ and driven by the Brownian increments $\xi_k$ and averaged increments $\zeta_k$ of the grid. Then for every $\varepsilon>0$
--
--   $$P\Big(\sup_{s\le T}|X_s|\le R,\ |X_T-(Y_n)_{j_n}|^2>\varepsilon\Big)\to0.$$
--
--   Role: convergence in probability of the discretisation to the SDE on the event that the solution stays in the ball, used to pass from the discrete minorisation to the transition kernel.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Lemma 3.6 in the Appendix (p. 32: overlap of transition probabilities of a nondegenerate diffusion started in a compact set); the steering (control) coupling and its tracking estimate follow the Girsanov coupling of M. Hairer, J. C. Mattingly, M. Scheutzow, Asymptotic coupling and a general form of Harris' theorem with applications to stochastic delay equations, Probab. Theory Related Fields 149 (2011) 223-259, https://doi.org/10.1007/s00440-009-0250-6, Section 2; discrete-time version via Doob's L2 maximal inequality for the martingale part and a discrete Gronwall bound.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem euler_chain_close_in_probability {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    (T : ℝ≥0) {hn : ℕ → ℝ≥0} (hpos : ∀ n, 0 < (hn n : ℝ))
    (hlim : Tendsto (fun n => (hn n : ℝ)) atTop (𝓝 0))
    (j : ℕ → ℕ) (hj : ∀ n, (T : ℝ) = j n * (hn n : ℝ)) {ε : ℝ} (hε : 0 < ε)
    (Y : ℕ → Ω → ℕ → SDEState d × SDEState d) (hY0 : ∀ n ω, Y n ω 0 = (x₀, x₀))
    (hY : ∀ n ω k, Y n ω (k + 1) = ((Y n ω k).2, (Y n ω k).2 + WithLp.toLp 2 (fun i =>
      ∑ j', (s₁ (Y n ω k).1 (i, j') *
          (W (((k : ℝ) * hn n).toNNReal + hn n) ω j' - W ((k : ℝ) * hn n).toNNReal ω j') +
        (s₁ (Y n ω k).2 (i, j') - s₁ (Y n ω k).1 (i, j')) * ((1 / (hn n : ℝ)) *
          ∫ u in (0 : ℝ)..(hn n : ℝ), (W (((k : ℝ) * hn n).toNNReal + hn n) ω j' -
            W (((k : ℝ) * hn n).toNNReal + u.toNNReal) ω j'))) +
        (hn n : ℝ) / 2 * (b₁ (Y n ω k).1 i + b₁ (Y n ω k).2 i)))) :
    Tendsto (fun n => P {ω | (∀ s ≤ T, ‖X s ω‖ ≤ R) ∧ ε < ‖X T ω - (Y n ω (j n)).2‖ ^ 2})
      atTop (𝓝 0) := by sorry

end EthierKurtz
