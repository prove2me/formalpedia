-- Prove2me | Theorems.Thm_CompoundSMM_Conv_lipschitz_display_p13
-- name    : CompoundSMM.Conv.lipschitz_display_p13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:31.058824+00:00
-- url     : https://prove2.me/theorems/49099f4b-16bb-4f00-bfeb-7f87370dd097
-- title:
--   Proof of Theorem 5, p. 13 — |V̂_{N_ν}(x; x^ν) − V̂_{∞;N_ν}(x; x^∞)| ≤ Lip_ψ Lip_φ (ε/N_ν)[Σ_t L(ξ^t) + Σ_s L(η^s)]
-- statement:
--   Assume (A2). Let $N\ge1$, $\varepsilon>0$, $L:\Xi\to\mathbb R$, a point $x$, samples $\xi^1,\dots,\xi^N$, $\eta^1,\dots,\eta^N$, and two families of selected surrogates $\widehat G^t,\widehat G^{t,\infty}$ (values in $\mathbb R^{\ell_G}$) and $\widehat F^s,\widehat F^{s,\infty}$ (values in $\mathbb R^{\ell_F}$) satisfying (13) at $x$:
--
--   $$\|\widehat G^t(x)-\widehat G^{t,\infty}(x)\|\le\varepsilon L(\xi^t),\qquad\|\widehat F^s(x)-\widehat F^{s,\infty}(x)\|\le\varepsilon L(\eta^s)\qquad(t,s=1,\dots,N).$$
--
--   Then the sample surrogates built from them, $\widehat V_N(x;x^\nu)=\psi\big(\frac1N\sum_t\varphi(\widehat G^t(x),\frac1N\sum_s\widehat F^s(x))\big)$ and $\widehat V_{\infty;N}(x;x^\infty)$ (the same with $\widehat G^{t,\infty},\widehat F^{s,\infty}$, display (14)), satisfy
--
--   $$\big|\widehat V_N(x;x^\nu)-\widehat V_{\infty;N}(x;x^\infty)\big|\ \le\ \mathrm{Lip}_\psi\,\mathrm{Lip}_\varphi\,\frac{\varepsilon}{N}\Big[\sum_{t=1}^N L(\xi^t)+\sum_{s=1}^N L(\eta^s)\Big].$$
--
--   In the proof of Theorem 5 this, with the law of large numbers for $L$, shows that the sample surrogates at $x^\nu$ and at the limit point $x^\infty$ merge along the subsequence $\mathcal K$.
--
--   **Formalization Note.** Only the Lipschitz parts of (A2) are used; the statement is about the values at the fixed point $x$, so the surrogates are given as arbitrary maps satisfying (13). Sample indices are 0-based.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, p. 13, proof of Theorem 5, the display following (14) (hypothesis (13))

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

namespace CompoundSMM.Conv

/-- Proof of Theorem 5, p. 13: if the selected surrogates at `x` satisfy (13),
`‖Ĝ^t(x) − Ĝ^{t,∞}(x)‖ ≤ ε L(ξ^t)` and `‖F̂^s(x) − F̂^{s,∞}(x)‖ ≤ ε L(η^s)` for `t, s < N`, then
`|V̂_N(x; x^ν) − V̂_{∞;N}(x; x^∞)| ≤ Lip_ψ Lip_φ (ε/N) [Σ_t L(ξ^t) + Σ_s L(η^s)]`. -/
theorem lipschitz_display_p13 {n ℓG ℓF ℓφ : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (Lψ Lφ : ℝ) (hA2 : A2 P Lψ Lφ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (L : Ξ → ℝ) (ξs ηs : ℕ → Ξ) (x : E n)
    (gs ginf : ℕ → E n → E ℓG) (fs finf : ℕ → E n → E ℓF)
    (h13G : ∀ t < N, ‖gs t x - ginf t x‖ ≤ ε * L (ξs t))
    (h13F : ∀ s < N, ‖fs s x - finf s x‖ ≤ ε * L (ηs s)) :
    |VN P N gs fs x - VN P N ginf finf x|
      ≤ Lψ * Lφ * (ε / N) *
          (∑ t ∈ Finset.range N, L (ξs t) + ∑ s ∈ Finset.range N, L (ηs s)) := by sorry

end CompoundSMM.Conv
