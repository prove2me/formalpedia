-- Prove2me | Theorems.Thm_CompoundSMM_Conv_proposition_2c
-- name    : CompoundSMM.Conv.proposition_2c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:28.577463+00:00
-- url     : https://prove2.me/theorems/fca093bd-8951-4003-9598-62b26329f143
-- title:
--   Proposition 2(c), p. 10 — E|Θ̄_{n,m}(x) − Θ(x)|² ≤ Lip_ψ² Lip_φ² ℓ_φ (σ_F²/m + σ_F²/(mn) + σ_G²/n), and E|Θ̄_{n,m}(x) − Θ(x)| ≤ C₁/min{m,n}^{1/2}
-- statement:
--   Let $\xi^1,\xi^2,\dots$ and $\eta^1,\eta^2,\dots$ be random variables on a probability space $(\Omega,\mathbb P)$ that are jointly independent, each with the law $\mu$ of $\tilde\xi$. Assume (A1), (A2) with constants $\mathrm{Lip}_\psi,\mathrm{Lip}_\varphi$, and (A4) with constants $\sigma_F,\sigma_G$. Then for every $x\in X$ and all integers $n,m\ge1$, the squared SAA error $|\overline\Theta_{n,m}(x)-\Theta(x)|^2$ is integrable,
--
--   $$\mathbb E\,\big|\overline\Theta_{n,m}(x)-\Theta(x)\big|^2\ \le\ (\mathrm{Lip}_\psi)^2(\mathrm{Lip}_\varphi)^2\,\ell_\varphi\Big(\frac{\sigma_F^2}{m}+\frac{\sigma_F^2}{mn}+\frac{\sigma_G^2}{n}\Big),$$
--
--   and
--
--   $$\mathbb E\,\big|\overline\Theta_{n,m}(x)-\Theta(x)\big|\ \le\ \frac{C_1}{\min\{m,n\}^{1/2}},\qquad C_1=\mathrm{Lip}_\psi\,\mathrm{Lip}_\varphi\,\sqrt{\ell_\varphi}\,\sqrt{2\sigma_F^2+\sigma_G^2}.$$
--
--   Here $\overline\Theta_{n,m}$ is the sample average approximation (9) built from the first $n$ samples $\xi^t$ and the first $m$ samples $\eta^s$. Since the bounds hold for every $x\in X$, they hold for the supremum over $X$, which is how the paper states them.
--
--   This is the non-asymptotic mean-square error bound for the compound SAA; it bounds the expected error terms $e_{\nu,i}$ in the convergence proof of the SMM algorithm.
--
--   **Formalization Note.** The constant $C_1$ is the one computed in the paper's appendix (p. 45); the page itself only says "some positive constant $C_1$". Norms are Euclidean. Parts (a) and (b) of Proposition 2 are not formalized.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, p. 10, Proposition 2(c); constant C₁ from the proof in the appendix, p. 45

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

namespace CompoundSMM.Conv

open MeasureTheory ProbabilityTheory

/-- Proposition 2(c), p. 10 (constant `C₁` from the appendix, p. 45): for independent i.i.d.
samples with law `μ`, under (A1), (A2) and (A4), for every `x ∈ X` and `n, m ≥ 1`,
`E|Θ̄_{n,m}(x) − Θ(x)|² ≤ Lip_ψ² Lip_φ² ℓ_φ (σ_F²/m + σ_F²/(mn) + σ_G²/n)` and
`E|Θ̄_{n,m}(x) − Θ(x)| ≤ C₁ / min{m, n}^{1/2}` with
`C₁ = Lip_ψ Lip_φ √ℓ_φ √(2σ_F² + σ_G²)`. -/
theorem proposition_2c {n ℓG ℓF ℓφ : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (Lψ Lφ σF σG : ℝ) (hA1 : A1 P) (hA2 : A2 P Lψ Lφ)
    (hA4 : A4 P σF σG) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ξs ηs : ℕ → Ω → Ξ)
    (hiid : IIDSamples Pr P.μ ξs ηs) (x : E n) (hx : x ∈ P.X) (nn m : ℕ) (hn : 0 < nn)
    (hm : 0 < m) :
    Integrable (fun ω => (Θbar P nn m (fun t => ξs t ω) (fun s => ηs s ω) x - Θ P x) ^ 2) Pr ∧
    ∫ ω, (Θbar P nn m (fun t => ξs t ω) (fun s => ηs s ω) x - Θ P x) ^ 2 ∂Pr
      ≤ Lψ ^ 2 * Lφ ^ 2 * (ℓφ : ℝ) *
          (σF ^ 2 / (m : ℝ) + σF ^ 2 / ((m : ℝ) * nn) + σG ^ 2 / (nn : ℝ)) ∧
    ∫ ω, |Θbar P nn m (fun t => ξs t ω) (fun s => ηs s ω) x - Θ P x| ∂Pr
      ≤ Lψ * Lφ * Real.sqrt ℓφ * Real.sqrt (2 * σF ^ 2 + σG ^ 2)
          / Real.sqrt (min (m : ℝ) (nn : ℝ)) := by sorry

end CompoundSMM.Conv
