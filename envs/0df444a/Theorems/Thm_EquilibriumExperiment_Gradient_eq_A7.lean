-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_eq_A7
-- name    : EquilibriumExperiment.Gradient.eq_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:36.770377+00:00
-- url     : https://prove2.me/theorems/7d20f33c-bc55-4e3a-846c-09532195243a
-- title:
--   (A.7), proof of Theorem 6, p. 38 (corrected: Υ̂ in probability) — D̄ → d_a, Z̄ → μ_a(p), Δ̂ → Δ_a(p) in L₂
-- statement:
--   Under the standing assumptions, fix a payment $p > 0$ with $\mathbb E[f_B(p\,\bar\omega)] > 0$, constants $\zeta > 0$ and $0 < \alpha < 1/2$, and run the $n$-th experiment with $\zeta_n$-perturbed payments, $\zeta_n = \zeta n^{-\alpha}$. Then, as $n \to \infty$,
--   $$\bar D \to d,\qquad \bar Z \to \mu(p),\qquad \hat\Delta \to \Delta(p) \quad \text{in } L_2,$$
--   and $\hat\Upsilon \to \mu'(p)$ in probability: for every $\varepsilon > 0$, $\mathbb P\bigl(|\hat\Upsilon - \mu'(p)| > \varepsilon\bigr) \to 0$.
--
--   Here $\bar D = D/n$, $\bar Z = \frac1n\sum_i Z_i$, $\hat\Delta$ is the regression coefficient (4.1) and $\hat\Upsilon$ the interference-corrected estimate (4.2); $\mu(p)$, $\Delta(p)$ and $\mu'(p)$ are the mean-field supply, marginal response (3.19) and supply gradient (3.20). These consistency statements, combined with Proposition 12, give the goal theorem.
--
--   **Formalization Note** The paper states all four convergences in $L_2$. For $\hat\Upsilon$ that is false in general: on the event $\hat\Delta < 0$, which has positive probability, the denominator $1 + p\bar D\hat\Delta\,\omega'(\bar D/\bar Z)/(\bar Z^2\omega(\bar D/\bar Z))$ vanishes at some demand level, and if the demand law has a density there, $\hat\Upsilon$ is not square integrable. The proof only uses convergence in probability (via Slutsky's lemma), so the $\hat\Upsilon$ part is stated in probability. $L_2$ convergence is `eLpNorm (· − limit) 2 → 0`, which is $+\infty$ for a function outside $L_2$. Each $n$ has its own sample space, so convergence in probability is a limit of the measures of the deviation sets. Divisions by $\bar Z = 0$ or by $\sum_i(\varepsilon_i - \bar\varepsilon)^2 = 0$ take Lean's value $0$; they occur on events of vanishing probability. The statement is conditional on the global state $A = a$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 38, proof of Theorem 6, display (A.7), with (A.4)–(A.6)

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem eq_A7 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n => Dbar n x - M.d) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.Zbar n p (ζ * (n : ℝ) ^ (-α)) x - M.muLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.DeltaHat n p (ζ * (n : ℝ) ^ (-α)) x - M.DeltaLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α)))
        {x | ε < |M.UpsHat n p (ζ * (n : ℝ) ^ (-α)) x - M.muLimDeriv p|}) atTop (𝓝 0) := by sorry

end EquilibriumExperiment.Gradient
