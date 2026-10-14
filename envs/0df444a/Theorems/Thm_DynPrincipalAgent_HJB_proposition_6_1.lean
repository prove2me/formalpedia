-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_proposition_6_1
-- name    : DynPrincipalAgent.HJB.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:33:31.345588+00:00
-- url     : https://prove2.me/theorems/dc89b2b0-8dc4-461a-ae8d-19696759e250
-- title:
--   Proposition 6.1 (i), p. 31 — P^{ζ,Z}(τ_n < T) ≤ C/n: only finitely many agents quit
-- statement:
--   Let Assumptions 2.2 and 3.1 hold. There is a constant $C>0$ depending only on $T$, $C_0$, $\Lambda_0$, $\Lambda_1$ such that for every type $\theta$, every $(t,x)\in D_\theta$ and every $(\eta,Z,\zeta)\in\mathcal A^{\infty,\theta}_{t,x}$ with quitting times $\{\tau_i\}$ as in (5.8),
--   $$\mathbb P^{\zeta,Z}(\tau_n<T)\le\frac Cn\quad\text{for all }n\ge1,\qquad\text{and consequently}\qquad\mathbb P^{\zeta,Z}\big(\tau_n<T\ \text{for all }n\big)=0.$$
--
--   Because each agent's quitting cost is at least $1/\Lambda_0$ and the barriers are regular, every agent stays for a while; the principal therefore sees only finitely many quittings, and the constraint $\lim_i\tau_i=T$ in (6.1) is redundant.
--
--   **Formalization Note.** $C$ is chosen before the model and is uniform over types, starting points, controls and $n$. $\mathbb P^{\zeta,Z}$ is the Girsanov measure built from the Itô integral of $I^h(\zeta;\cdot,Z)$; the bounds are on the (outer) measure of the events.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Proposition 6.1 (i), (6.3), p. 31

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Viscosity
import Definitions.Def_DynPrincipalAgent_HJB_Controls
import Definitions.Def_DynPrincipalAgent_HJB_Quitting

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Peng1990.SMP

namespace DynPrincipalAgent.HJB

theorem proposition_6_1 : ∀ (T : ℝ≥0) (C₀ Λ₀ Λ₁ : ℝ), ∃ C : ℝ, 0 < C ∧
    ∀ {Θ : Type} [MeasurableSpace Θ] (M : Model Θ),
      M.T = T → M.C₀ = C₀ → M.Λ₀ = Λ₀ → M.Λ₁ = Λ₁ → M.Standing →
    ∀ {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ) (t : ℝ≥0) (x : ℝ),
      ((t : ℝ), x) ∈ M.D θ →
      ∀ (η Z : ℝ≥0 → Ω → ℝ) (ζ : ℝ≥0 → Ω → Θ) (J : ℝ≥0 → Ω → ℝ) (τ : ℕ → Ω → ℝ≥0)
        (X : ℝ≥0 → Ω → ℝ), M.InAinf S θ t x η Z ζ J τ X →
      ∀ I : ℝ≥0 → Ω → ℝ, IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha ζ Z)) I →
        (∀ n : ℕ, 1 ≤ n →
          M.girsanov S t (M.alpha ζ Z) I {ω | τ n ω < M.T} ≤ ENNReal.ofReal (C / n)) ∧
        M.girsanov S t (M.alpha ζ Z) I {ω | ∀ n : ℕ, 1 ≤ n → τ n ω < M.T} = 0 := by sorry

end DynPrincipalAgent.HJB
