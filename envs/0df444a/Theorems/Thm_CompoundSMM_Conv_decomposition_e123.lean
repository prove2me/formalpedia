-- Prove2me | Theorems.Thm_CompoundSMM_Conv_decomposition_e123
-- name    : CompoundSMM.Conv.decomposition_e123
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:28.479402+00:00
-- url     : https://prove2.me/theorems/cd5c04f6-d759-4342-aee1-14e6d6765171
-- title:
--   Proof of Theorem 5, pp. 11–12 — Θ̄_{N_ν}(x) − Θ̄_{N_{ν−1}}(x) ≤ e_{ν,1} + e_{ν,2} + e_{ν,3} (sign of e_{ν,1}'s coefficient corrected)
-- statement:
--   Assume (A2). Let $x\in\mathbb R^n$, samples $\xi^1,\xi^2,\dots$ and $\eta^1,\eta^2,\dots$ in $\Xi$, and integers $0<N'<N$ (in the paper $N'=N_{\nu-1}$, $N=N_\nu$, $x=x^\nu$). Then
--
--   $$\overline\Theta_{N}(x)-\overline\Theta_{N'}(x)\ \le\ e_1+e_2+e_3,$$
--
--   where $\overline\Theta_M=\overline\Theta_{M,M}$ is the sample average approximation (9) and
--
--   $$e_1=\Big(1-\frac{(N')^2}{N^2}\Big)\Big|\overline\Theta_{N'}(x)-\Theta(x)\Big|,$$
--
--   $$e_2=\frac{N'(N-N')}{N^2}\Big|\psi\Big(\frac1{N-N'}\sum_{t=N'+1}^{N}\varphi\Big(G(x,\xi^t),\frac1{N'}\sum_{s=1}^{N'}F(x,\eta^s)\Big)\Big)-\Theta(x)\Big|,$$
--
--   $$e_3=\Big(1-\frac{N'}{N}\Big)\Big|\psi\Big(\frac1{N}\sum_{t=1}^{N}\varphi\Big(G(x,\xi^t),\frac1{N-N'}\sum_{s=N'+1}^{N}F(x,\eta^s)\Big)\Big)-\Theta(x)\Big|.$$
--
--   The three error terms separate the effect of the old samples, the new $\xi$-samples and the new $\eta$-samples when the sample size grows from $N'$ to $N$; their expectations are bounded by Proposition 2(c) and summed with Lemma 3 in the convergence proof.
--
--   **Formalization Note.** The page prints the coefficient of $e_{\nu,1}$ as $\big((N_{\nu-1})^2/(N_\nu)^2-1\big)$, which is $\le0$; with it the inequality is false ($\psi=\varphi=\mathrm{id}$, $\ell_F=0$, $N'=1$, $N=2$, $G(x,\xi^1)=0$, $G(x,\xi^2)=2$, $\Theta(x)=1$ gives left side $1$ and printed right side $-1/2$). The coefficient here is $1-(N')^2/N^2$, the one used in (12) and consistent with the page's statement that the $e_{\nu,i}$ are nonnegative. Sample indices are 0-based: the new samples are those with index in $[N',N)$.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, pp. 11–12, proof of Theorem 5, definition of e_{ν,1}, e_{ν,2}, e_{ν,3} (coefficient of e_{ν,1} corrected)

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

namespace CompoundSMM.Conv

/-- Proof of Theorem 5, pp. 11–12: with `N' = N_{ν−1} < N = N_ν`,
`Θ̄_N(x) − Θ̄_{N'}(x) ≤ e₁ + e₂ + e₃`, where the coefficient of `e₁` is `1 − (N')²/N²`
(the page prints `(N')²/N² − 1`, a sign slip). Sample indices are 0-based; the new samples are
those with index in `[N', N)`. -/
theorem decomposition_e123 {n ℓG ℓF ℓφ : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (Lψ Lφ : ℝ) (hA2 : A2 P Lψ Lφ)
    (ξs ηs : ℕ → Ξ) (x : E n) (N' N : ℕ) (hN' : 0 < N') (hlt : N' < N) :
    Θbar P N N ξs ηs x - Θbar P N' N' ξs ηs x ≤
      (1 - ((N' : ℝ) ^ 2 / (N : ℝ) ^ 2)) * |Θbar P N' N' ξs ηs x - Θ P x| +
      (N' : ℝ) * ((N : ℝ) - N') / (N : ℝ) ^ 2 *
        |P.ψ ((1 / ((N : ℝ) - N')) • ∑ t ∈ Finset.Ico N' N,
            P.φ (P.G x (ξs t)) ((1 / (N' : ℝ)) • ∑ s ∈ Finset.range N', P.F x (ηs s)))
          - Θ P x| +
      (1 - (N' : ℝ) / N) *
        |P.ψ ((1 / (N : ℝ)) • ∑ t ∈ Finset.range N,
            P.φ (P.G x (ξs t)) ((1 / ((N : ℝ) - N')) • ∑ s ∈ Finset.Ico N' N, P.F x (ηs s)))
          - Θ P x| := by sorry

end CompoundSMM.Conv
