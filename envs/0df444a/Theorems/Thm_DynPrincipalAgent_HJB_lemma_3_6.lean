-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_lemma_3_6
-- name    : DynPrincipalAgent.HJB.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:36:08.765129+00:00
-- url     : https://prove2.me/theorems/71fd4886-68d8-48a8-bbfe-938fdc019a92
-- title:
--   Lemma 3.6, p. 15 — ū₀ is bounded, uniformly continuous with modulus C√ρ, and ū₀(T) = −c^P_T
-- statement:
--   Let Assumptions 2.2 and 3.1 hold. There is a constant $C>0$ depending only on $T$, $C_0$, $\Lambda_0$, $\Lambda_1$ such that the new-hire value
--   $$\overline u_0(t)=\sup_{\tilde\theta\in\Theta}V^P_0(\tilde\theta;t)-c^P_t$$
--   satisfies:
--   1. for every $t\in[0,T]$ the family $\{V^P_0(\tilde\theta;t)\}_{\tilde\theta}$ is bounded above;
--   2. $|\overline u_0(s)-\overline u_0(t)|\le C\sqrt{\rho(|s-t|)}$ for $s,t\in[0,T]$;
--   3. $\overline u_0$ is bounded on $[0,T]$;
--   4. $\overline u_0(T)=-c^P_T$.
--
--   **Formalization Note.** Item 1 makes the supremum over types a genuine one; the paper presupposes it. $C$ is chosen before the model.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Lemma 3.6, p. 15

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Viscosity
import Definitions.Def_DynPrincipalAgent_HJB_Controls
import Definitions.Def_DynPrincipalAgent_HJB_Quitting
import Definitions.Def_DynPrincipalAgent_HJB_SelfEnforcing

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Peng1990.SMP

namespace DynPrincipalAgent.HJB

theorem lemma_3_6 : ∀ (T : ℝ≥0) (C₀ Λ₀ Λ₁ : ℝ), ∃ C : ℝ, 0 < C ∧
    ∀ {Θ : Type} [MeasurableSpace Θ] (M : Model Θ),
      M.T = T → M.C₀ = C₀ → M.Λ₀ = Λ₀ → M.Λ₁ = Λ₁ → M.Standing →
    ∀ {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω),
      (∀ t ∈ Icc (0 : ℝ) M.T, BddAbove (Set.range fun θ : Θ => M.V0P S θ t)) ∧
      (∀ s ∈ Icc (0 : ℝ) M.T, ∀ t ∈ Icc (0 : ℝ) M.T,
        |M.u0bar S s - M.u0bar S t| ≤ C * Real.sqrt (M.ρ |s - t|)) ∧
      (∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) M.T, |M.u0bar S t| ≤ K) ∧
      M.u0bar S M.T = -M.cP M.T := by sorry

end DynPrincipalAgent.HJB
