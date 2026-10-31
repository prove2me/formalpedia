-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_eq_A7_Zbar
-- name    : EquilibriumExperiment.Gradient.eq_A7_Zbar
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T13:27:21.157441+00:00
-- url     : https://prove2.me/theorems/2c5528cf-a627-4292-bca1-e834cf10436e
-- title:
--   (A.7), proof of Theorem 6, p. 38 — $\bar Z\to\mu_a(p)$ in $L_2$ under $\zeta_n$-perturbed payments
-- statement:
--   Consider a market satisfying the standing assumptions (Definition 5, Assumptions 1–3, (3.1)–(3.2)), conditional on a global state $A=a$. Fix $p>0$ with $\mathbb E[f_B(p\,\bar\omega)]>0$ (so that $\mu_a(p)$ exists, Lemma 2), and constants $\zeta>0$, $0<\alpha<1/2$. In the $n$-th system, supplier $i$ is paid $P_i=p+\zeta_n\varepsilon_i$ with independent signs $\varepsilon_i=\pm1$ and $\zeta_n=\zeta n^{-\alpha}$, and suppliers respond in equilibrium, with activity indicators $Z_i$ (Lemma 1). Then the active fraction $\bar Z=\frac1n\sum_{i=1}^n Z_i$ converges in $L_2$ to the mean-field active supply:
--   $$\lim_{n\to\infty}\mathbb E\bigl[(\bar Z-\mu_a(p))^2\bigr]^{1/2}=0 .$$
--   This is the second of the four limits in (A.7). Here $\mu_a(p)$ is the unique solution in $(0,1]$ of $\mu=\mathbb E[f_{B_1}(p\,\omega(d_a/\mu))]$, and the $L_2$ norm is taken under the law of the $n$-th experiment.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, Appendix A.4 (proof of Theorem 6), p. 38, eq. (A.7), second limit Z̄ → μ_a(p)

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem eq_A7_Zbar {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.Zbar n p (ζ * (n : ℝ) ^ (-α)) x - M.muLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) := by sorry

end EquilibriumExperiment.Gradient
