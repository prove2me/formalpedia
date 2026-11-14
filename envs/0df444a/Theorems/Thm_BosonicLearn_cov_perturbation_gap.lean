-- Prove2me | Theorems.Thm_BosonicLearn_cov_perturbation_gap
-- name    : BosonicLearn.cov_perturbation_gap
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:49:37.189325+00:00
-- url     : https://prove2.me/theorems/df8cc679-4cde-4095-a77f-257ab3160a4a
-- title:
--   One-sided relative covariance bound under a Loewner gap: $\frac12\|\rho(\mu,\Sigma')-\rho(\mu,\Sigma)\|_1\le\sqrt2\,K_\nu\,\Delta_{\rm rel}$ for $\Sigma\succeq(\frac12+\nu)I$, $\Sigma'\succeq\Sigma$
-- statement:
--   Theorem 7 in the form used in the proof of Theorem 8, proved without relative entropy.
--
--   Let $\rho(\mu,\Sigma)$ and $\rho(\mu,\Sigma')$ be $n$-mode Gaussian states with the same mean, $\Sigma\succeq(\frac12+\nu)\mathbf 1$ for some $\nu>0$, and $\Sigma'\succeq\Sigma$. With $\Delta_{\rm rel}=\|\Sigma^{-1/2}(\Sigma'-\Sigma)\Sigma^{-1/2}\|_F$ and $K_\nu=\frac{\frac12+\nu}{\sqrt{\nu(1+\nu)}}$,
--
--   $$\tfrac12\big\|\rho(\mu,\Sigma')-\rho(\mu,\Sigma)\big\|_1\ \le\ \sqrt2\,K_\nu\,\Delta_{\rm rel}.$$
--
--   Comparison with `BosonicLearn.theorem_7`: the hypothesis on the symplectic eigenvalues ($\ge\nu_-$) is replaced by the Loewner inequality $\Sigma\succeq(\frac12+\nu)\mathbf 1$, which implies it with $\nu_-=\frac12+\nu$ and is the promise of Theorems 3 and 8; the mean is arbitrary but common; and the constant $\frac{1}{2\sqrt{2\gamma_-}}=\frac14\sqrt{2+1/\nu}$ is replaced by $\sqrt2K_\nu\le4\cdot\frac14\sqrt{2+1/\nu}$. The scaling $\sqrt{1+1/\nu}$ is the same. (The proof gives $\frac12K_\nu\Delta_{\rm rel}$ when $K_\nu\Delta_{\rm rel}\le1/\sqrt2$.)
--
--   Proof idea. Both states are Gaussian mixtures of displaced thermal states $\tau$ of covariance $(\frac12+\nu)\mathbf 1$. The extra noise $x\sim\mathcal N(0,\Sigma'-\Sigma)$ is split as $(\Sigma-a)\Sigma^{-1}x+a\Sigma^{-1}x$, $a=\frac12+\nu$: the first part is absorbed by a Cameron–Martin weight, the second displaces $\tau$. The trace norm is bounded by duality (`BosonicLearn.traceSize_le_of_pairing`) and a Cauchy–Schwarz inequality weighted by $\tau$; the kernel identity `BosonicLearn.thermal_displaced_kernel` turns the resulting $\chi^2$ quantity into $\mathbb E\exp(g^TMg')-1\le\operatorname{Tr}M^2\le K_\nu^2\Delta_{\rm rel}^2$ (`BosonicLearn.gaussian_bilinear_exp_bound`).
--
--   **Formalization Note** $\Delta_{\rm rel}^2$ is `(S⁻¹ * (S' - S) * S⁻¹ * (S' - S)).trace`; hypotheses `(S - (1/2 + ν) • 1).PosSemidef`, `(S' - S).PosSemidef`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §7.1, Theorem 7, Eqs. (184)–(185), p. 55; proof of Theorem 8, p. 61

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **One-sided relative covariance bound under a Loewner gap: `½‖ρ(µ, Σ′) − ρ(µ, Σ)‖₁ ≤ √2 K_ν Δ_rel`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 7, Eqs. (184)–(185), p. 55: "Let Σ̄ be an n-mode covariance matrix whose symplectic eigenvalues are all at
least ν₋ > 1/2, and let Σ′ be another covariance matrix satisfying Σ′ ⪰ Σ̄. … Then
½‖ρ(0, Σ′) − ρ(0, Σ̄)‖₁ ≤ (1/(2√(2γ₋))) Δ_rel", in the form used in the proof of Theorem 8 (p. 61), where
`Σ̄ ⪰ (½ + ν)I`.

Let `ρ(µ, Σ)` and `ρ(µ, Σ′)` be Gaussian states with the same mean, `Σ ⪰ (½ + ν)I` for some `ν > 0`, and `Σ′ ⪰ Σ`.
With `Δ_rel = ‖Σ^{−1/2}(Σ′ − Σ)Σ^{−1/2}‖_F` and `K_ν = (½ + ν)/√(ν(1 + ν))`,

`½‖ρ(µ, Σ′) − ρ(µ, Σ)‖₁ ≤ √2 · K_ν · Δ_rel`.

**Formalization Note.** This is Theorem 7 with the hypothesis on the symplectic eigenvalues replaced by the Loewner
inequality `Σ ⪰ (½ + ν)I` (which implies it, and is the promise of Theorems 3 and 8), a common mean `µ`, and the
constant `1/(2√(2γ₋)) = ¼√(2 + 1/ν)` replaced by `√2 K_ν ≤ 4 · ¼√(2 + 1/ν)`; the scaling `√(1 + 1/ν)` is the same.
`Δ_rel² = Tr(Σ⁻¹(Σ′ − Σ)Σ⁻¹(Σ′ − Σ))`. It is proved without relative entropy: both states are Gaussian mixtures of
displaced thermal states of covariance `(½ + ν)I`, and the trace norm is bounded by a `χ²`-divergence relative to
that thermal state (`thermal_displaced_kernel`, `gaussian_bilinear_exp_bound`, `traceSize_le_of_pairing`). -/
theorem cov_perturbation_gap {n : ℕ} (ρ ρ' : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (ν : ℝ) (hν : 0 < ν)
    (hS : (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (hord : (S' - S).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ S') :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) *
        Real.sqrt (S⁻¹ * (S' - S) * S⁻¹ * (S' - S)).trace) := by sorry

end BosonicLearn
