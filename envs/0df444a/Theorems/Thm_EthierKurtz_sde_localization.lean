-- Prove2me | Theorems.Thm_EthierKurtz_sde_localization
-- name    : EthierKurtz.sde_localization
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:50:52.859854+00:00
-- url     : https://prove2.me/theorems/edda9e73-28ee-4f70-bf47-92c043134f95
-- title:
--   Localization for Brownian SDEs: agreement up to the exit time of a ball, and gluing a consistent non-exploding family
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion and $x_0\in\mathbb R^d$.
--
--   (i) If $(\sigma_1,b_1)$ and $(\sigma_2,b_2)$ are continuous and bounded by $S$, $(\sigma_1,b_1)$ is $L$-Lipschitz on $\{\|x\|\le R+3\}$ and the two coefficient pairs agree there, then solutions $X,Y$ from $x_0$ satisfy
--
--   $$X_t=Y_t\quad\text{for all } t \text{ with } \sup_{s\le t}\|X_s\|\le R,\ \text{a.s.}$$
--
--   (ii) If $(s^N,b^N)$ agree with continuous $(\sigma,b)$ on $\{\|x\|\le N\}$, $Y^N$ solves the $N$-th equation, $Y^N=Y^{N'}$ up to the exit of $Y^N$ from $\{\|x\|\le N\}$ ($N\le N'$), and a.s. every horizon $T$ is covered by some $N$ with $\sup_{s\le T}\|Y^N_s\|\le N$, then the equation with coefficients $(\sigma,b)$ has a strong solution from $x_0$.
--
--   Role: the localization argument that turns solutions of truncated equations into a global solution of the Kolmogorov system once non-explosion is known.
-- source:
--   I. Karatzas, S. E. Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113, 1991, https://doi.org/10.1007/978-1-4612-0949-2, Section 5.2, proof of Theorem 5.2.5 (comparison of two solutions up to the exit time of a ball where the coefficients are Lipschitz) and the localization by truncated coefficients used with Theorem 5.2.9, pp. 287-291

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

theorem sde_localization {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    (x₀ : SDEState d) :
    (∀ (σ₁ σ₂ : SDEState d → SDEDiffusion d) (b₁ b₂ : SDEState d → SDEState d),
      Continuous σ₁ → Continuous b₁ → Continuous σ₂ → Continuous b₂ →
      ∀ R L S : ℝ, 0 ≤ R → 0 ≤ L →
      (∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
        ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₁ x - σ₁ y‖ ≤ L * ‖x - y‖) →
      (∀ x, ‖σ₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) → (∀ x, ‖σ₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S) →
      (∀ x : SDEState d, ‖x‖ ≤ R + 3 → σ₂ x = σ₁ x ∧ b₂ x = b₁ x) →
      ∀ X Y : ℝ≥0 → Ω → SDEState d,
      SolvesBrownianSDE P (fun p => σ₁ p.2) (fun p => b₁ p.2) W (fun _ => x₀) X →
      SolvesBrownianSDE P (fun p => σ₂ p.2) (fun p => b₂ p.2) W (fun _ => x₀) Y →
      ∀ᵐ ω ∂P, ∀ t, (∀ s ≤ t, ‖X s ω‖ ≤ R) → X t ω = Y t ω) ∧
    (∀ (σ : SDEState d → SDEDiffusion d) (b : SDEState d → SDEState d),
      Continuous σ → Continuous b →
      ∀ (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d),
      (∀ N, Continuous (s₁ N)) →
      (∀ (N : ℕ) (x : SDEState d), ‖x‖ ≤ (N : ℝ) → s₁ N x = σ x ∧ b₁ N x = b x) →
      ∀ Y : ℕ → ℝ≥0 → Ω → SDEState d,
      (∀ N, SolvesBrownianSDE P (fun p => s₁ N p.2) (fun p => b₁ N p.2) W (fun _ => x₀) (Y N)) →
      (∀ N N' : ℕ, N ≤ N' →
        ∀ᵐ ω ∂P, ∀ t, (∀ s ≤ t, ‖Y N s ω‖ ≤ N) → Y N t ω = Y N' t ω) →
      (∀ᵐ ω ∂P, ∀ T : ℕ, ∃ N : ℕ, ∀ s ≤ (T : ℝ≥0), ‖Y N s ω‖ ≤ N) →
      ∃ X : ℝ≥0 → Ω → SDEState d,
        SolvesBrownianSDE P (fun p => σ p.2) (fun p => b p.2) W (fun _ => x₀) X) := by sorry

end EthierKurtz
