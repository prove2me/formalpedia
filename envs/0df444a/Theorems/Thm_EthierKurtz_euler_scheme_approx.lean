-- Prove2me | Theorems.Thm_EthierKurtz_euler_scheme_approx
-- name    : EthierKurtz.euler_scheme_approx
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:08:50.970475+00:00
-- url     : https://prove2.me/theorems/6a27d612-b927-4e71-91eb-2aa952697c53
-- title:
--   Weak approximation of a locally Lipschitz SDE by a coefficient-interpolated Euler scheme, up to the exit probability
-- statement:
--   Let $X$ solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$, $X_0=x_0$, and let $s_1,b_1$ be globally bounded, globally $L$-Lipschitz and equal to $\sigma_0,b_0$ on $\bar B_{R+3}$. Let $h_n\downarrow 0$, $j_n h_n\le T\le (j_n+1)h_n$, and let $Z^n_k$ be the Euler scheme with step $h_n$ whose coefficients are interpolated linearly between the two last grid values (recursion hZs, $Z^n_{-1}=Z^n_0=x_0$). Then for uniformly bounded ($\le K$), uniformly $\Lambda$-Lipschitz $\varphi_n$ and every $\eta>0$, eventually
--
--   $$\Big|\mathbb E\,\varphi_n(Z^n_{j_n-1},Z^n_{j_n})-\mathbb E\,\varphi_n(X_T,X_T)\Big|\le 2K\,\mathbb P\big(\exists s\le T:\ |X_s|>R\big)+\eta .$$
--
--   Role: the Euler-scheme approximation through which the Chapman-Kolmogorov identity is transferred from the (exactly Markov) scheme to the SDE solution.
--
--   **Formalization Note**: the scheme carries the pair (previous, current) grid value; its coefficients are linear in time on each step so that the integrands are continuous.
-- source:
--   P. E. Kloeden, E. Platen, Numerical Solution of Stochastic Differential Equations, Springer 1992, https://doi.org/10.1007/978-3-662-12616-5, Section 14.1, Theorem 14.1.5 (weak convergence of the Euler scheme); D. J. Higham, X. Mao, A. M. Stuart, Strong convergence of Euler-type methods for nonlinear stochastic differential equations, SIAM J. Numer. Anal. 40 (2002) 1041-1063, https://doi.org/10.1137/S0036142901389530, Theorem 2.2 (locally Lipschitz coefficients, localization)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem euler_scheme_approx {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0))
    (T : ℝ≥0) (j : ℕ → ℕ)
    (hj : ∀ n, 1 ≤ j n ∧ (j n : ℝ) * hn n ≤ T ∧ (T : ℝ) ≤ j n * hn n + hn n)
    (φ : ℕ → SDEState d → SDEState d → ℝ) {K Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hφK : ∀ n a y, |φ n a y| ≤ K)
    (hφL : ∀ n a y a' y', |φ n a y - φ n a' y'| ≤ Λ * (‖a - a'‖ + ‖y - y'‖))
    {η : ℝ} (hη : 0 < η)
    (Z : ℕ → Ω → ℕ → SDEState d × SDEState d) (hZ0 : ∀ n ω, Z n ω 0 = (x₀, x₀))
    (hZs : ∀ n ω (k : ℕ), Z n ω (k + 1) = ((Z n ω k).2, (Z n ω k).2 + WithLp.toLp 2 fun i =>
      (∑ j', (s₁ (Z n ω k).1 (i, j') * (W ((k : ℝ) * hn n + hn n).toNNReal ω j' -
          W ((k : ℝ) * hn n).toNNReal ω j') +
        (s₁ (Z n ω k).2 (i, j') - s₁ (Z n ω k).1 (i, j')) / hn n *
          (hn n * W ((k : ℝ) * hn n + hn n).toNNReal ω j' -
            ∫ v in ((k : ℝ) * hn n)..((k : ℝ) * hn n + hn n), W v.toNNReal ω j'))) +
      b₁ (Z n ω k).1 i * hn n + (b₁ (Z n ω k).2 i - b₁ (Z n ω k).1 i) * hn n ^ 2 / (2 * hn n))) :
    ∀ᶠ n in atTop, |∫ ω, φ n (Z n ω (j n)).1
        (Z n ω (j n)).2 ∂P -
        ∫ ω, φ n (X T ω) (X T ω) ∂P| ≤
      2 * K * (P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R}ᶜ).toReal + η := by sorry

end EthierKurtz
