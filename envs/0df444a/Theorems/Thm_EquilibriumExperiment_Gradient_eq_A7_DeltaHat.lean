-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_eq_A7_DeltaHat
-- name    : EquilibriumExperiment.Gradient.eq_A7_DeltaHat
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T13:27:17.048481+00:00
-- url     : https://prove2.me/theorems/f6cf506b-013f-42e7-99fd-62ca674c5782
-- title:
--   (A.7), proof of Theorem 6, p. 38 — $\hat\Delta\to\Delta_a(p)$ in $L_2$ under $\zeta_n$-perturbed payments
-- statement:
--   Consider a market satisfying the standing assumptions (Definition 5, Assumptions 1–3, (3.1)–(3.2)), conditional on a global state $A=a$. Fix $p>0$ with $\mathbb E[f_B(p\,\bar\omega)]>0$ (so that $\mu_a(p)$ exists, Lemma 2), and constants $\zeta>0$, $0<\alpha<1/2$. In the $n$-th system, supplier $i$ is paid $P_i=p+\zeta_n\varepsilon_i$ with independent signs $\varepsilon_i=\pm1$ and $\zeta_n=\zeta n^{-\alpha}$, and suppliers respond in equilibrium, with activity indicators $Z_i$ (Lemma 1). Let $\hat\Delta=\zeta_n^{-1}\sum_i(Z_i-\bar Z)(\varepsilon_i-\bar\varepsilon)\big/\sum_i(\varepsilon_i-\bar\varepsilon)^2$ be the regression coefficient (4.1). Then $\hat\Delta$ converges in $L_2$ to the marginal response
--   $$\Delta_a(p)=\omega\bigl(d_a/\mu_a(p)\bigr)\,\mathbb E\bigl[f'_{B_1}\bigl(p\,\omega(d_a/\mu_a(p))\bigr)\bigr]\quad(3.19),$$
--   that is,
--   $$\lim_{n\to\infty}\mathbb E\bigl[(\hat\Delta-\Delta_a(p))^2\bigr]^{1/2}=0 .$$
--   This is the third of the four limits in (A.7). Its proof in the paper combines (A.9), Lemma 4 (3.19) and a variance bound that uses $\zeta_n\sqrt n\to\infty$, i.e. $\alpha<1/2$. Divisions by zero in (4.1) follow Lean's convention $x/0=0$; they occur only when all $\varepsilon_i$ are equal, an event of probability $2^{1-n}$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, Appendix A.4 (proof of Theorem 6), pp. 38–39, eq. (A.7), third limit Δ̂ → Δ_a(p) (using (A.9), (3.19))

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem eq_A7_DeltaHat {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.DeltaHat n p (ζ * (n : ℝ) ^ (-α)) x - M.DeltaLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) := by sorry

end EquilibriumExperiment.Gradient
