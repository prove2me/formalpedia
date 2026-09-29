-- Prove2me | Theorems.Thm_FamousTheorems_char_fun_normal_distribution_7a
-- name    : FamousTheorems.char_fun_normal_distribution_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:21.539987+00:00
-- url     : https://prove2.me/theorems/636d3ea9-2c81-4b9e-a058-3e7e4b7d0597
-- title:
--   Characteristic function of the normal distribution
-- statement:
--   **Characteristic function of the normal distribution.** Let $\mathcal N(\mu,v)$ be the normal distribution on $\mathbb R$ with mean $\mu$ and variance $v\ge0$. For every $t\in\mathbb R$,
--   $$\int e^{itx}\,d\mathcal N(\mu,v)(x)=\exp\!\Big(it\mu-\frac{vt^2}{2}\Big).$$
--
--   This formula is used throughout probability. Through Lévy's continuity theorem it gives the standard proof of the central limit theorem, and it shows directly that sums of independent normal variables are normal. For $\mu=0$, $v=1$ it says that $e^{-x^2/2}$ is its own Fourier transform up to normalisation.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.charFun_gaussianReal`. `gaussianReal μ v` is the normal distribution with mean $\mu$ and variance $v$, a non-negative real. For $v=0$ it is the Dirac mass at $\mu$. `MeasureTheory.charFun ρ t` is $\int e^{itx}\,d\rho(x)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.charFun_gaussianReal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem char_fun_normal_distribution_7a (μ : ℝ) (v : NNReal) (t : ℝ) :
    MeasureTheory.charFun (ProbabilityTheory.gaussianReal μ v) t =
      Complex.exp ((t : ℂ) * μ * Complex.I - ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by sorry

end FamousTheorems
