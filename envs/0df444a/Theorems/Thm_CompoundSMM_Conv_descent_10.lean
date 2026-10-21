-- Prove2me | Theorems.Thm_CompoundSMM_Conv_descent_10
-- name    : CompoundSMM.Conv.descent_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:23.036112+00:00
-- url     : https://prove2.me/theorems/727e8b0f-c956-465d-8542-18e3018e1344
-- title:
--   Proof of Theorem 5, (10), p. 11 — one SMM step: Θ̄_N(x⁺) + ‖x⁺ − x′‖²/(2ρ) ≤ V̂_N(x⁺; x′) + ‖x⁺ − x′‖²/(2ρ) ≤ V̂_N(x′; x′) = Θ̄_N(x′)
-- statement:
--   Assume (A2), (A3$_G$) and (A3$_F$). Let $\rho>0$, $N\ge1$, $x'\in X$, and samples $\xi^1,\dots,\xi^N$, $\eta^1,\dots,\eta^N\in\Xi$. For each $t$ and $s$ choose surrogates $\widehat G^t(\bullet,\xi^t;x')\in\mathcal G(x',\xi^t)$ and $\widehat F^s(\bullet,\eta^s;x')\in\mathcal F(x',\eta^s)$, form the sample surrogate
--
--   $$\widehat V_N(x;x')=\psi\Big(\frac1N\sum_{t=1}^N\varphi\Big(\widehat G^t(x,\xi^t;x'),\ \frac1N\sum_{s=1}^N\widehat F^s(x,\eta^s;x')\Big)\Big),$$
--
--   and let $x^+\in X$ minimize $\widehat V_N(\bullet;x')+\frac1{2\rho}\|\bullet-x'\|^2$ over $X$. Then
--
--   $$\overline\Theta_{N}(x^+)+\frac1{2\rho}\|x^+-x'\|^2\ \le\ \widehat V_N(x^+;x')+\frac1{2\rho}\|x^+-x'\|^2\ \le\ \widehat V_N(x';x')\ =\ \overline\Theta_N(x'),$$
--
--   where $\overline\Theta_N=\overline\Theta_{N,N}$ is the sample average approximation (9) on the same samples.
--
--   This is the descent inequality (10) that drives the convergence proof of the SMM algorithm: with $x'=x^\nu$ and $x^+=x^{\nu+1}$ the SAA objective plus the step length cannot exceed the SAA objective at the previous iterate.
--
--   **Formalization Note.** Sample indices are 0-based. The surrogates may depend on the sample index here (the page's $\widehat G^t$), since the step uses only touching and majorization.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, p. 11, proof of Theorem 5, display (10)

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

namespace CompoundSMM.Conv

/-- Display (10), proof of Theorem 5, p. 11: if `xnew ∈ X` minimizes the sample surrogate plus the
proximal term over `X`, then
`Θ̄_N(xnew) + ‖xnew − x′‖²/(2ρ) ≤ V̂_N(xnew; x′) + ‖xnew − x′‖²/(2ρ) ≤ V̂_N(x′; x′) = Θ̄_N(x′)`. -/
theorem descent_10 {n ℓG ℓF ℓφ : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (𝒢 : E n → Ξ → Set (E n → E ℓG))
    (ℱ : E n → Ξ → Set (E n → E ℓF)) (Lψ Lφ : ℝ) (hA2 : A2 P Lψ Lφ)
    (hA3G : SurrogateFamily P.X P.μ P.G 𝒢) (hA3F : SurrogateFamily P.X P.μ P.F ℱ)
    (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (hN : 0 < N) (ξs ηs : ℕ → Ξ) (x' : E n) (hx' : x' ∈ P.X)
    (gs : ℕ → E n → E ℓG) (fs : ℕ → E n → E ℓF)
    (hgs : ∀ t < N, gs t ∈ 𝒢 x' (ξs t)) (hfs : ∀ s < N, fs s ∈ ℱ x' (ηs s))
    (xnew : E n) (hxnew : xnew ∈ P.X)
    (hmin : ∀ y ∈ P.X, VN P N gs fs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ)
      ≤ VN P N gs fs y + ‖y - x'‖ ^ 2 / (2 * ρ)) :
    Θbar P N N ξs ηs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ)
        ≤ VN P N gs fs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ) ∧
      VN P N gs fs xnew + ‖xnew - x'‖ ^ 2 / (2 * ρ) ≤ VN P N gs fs x' ∧
      VN P N gs fs x' = Θbar P N N ξs ηs x' := by sorry

end CompoundSMM.Conv
