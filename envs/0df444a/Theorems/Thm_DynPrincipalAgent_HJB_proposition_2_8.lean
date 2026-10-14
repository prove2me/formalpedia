-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_proposition_2_8
-- name    : DynPrincipalAgent.HJB.proposition_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:36:46.139158+00:00
-- url     : https://prove2.me/theorems/398c6f5f-ea55-41b5-9407-369a90a9bea6
-- title:
--   Proposition 2.8, p. 12 — the self-enforcing value V^P_0(θ; ·) is uniformly continuous with modulus C√ρ
-- statement:
--   Let Assumptions 2.2 and 2.7 hold. There is a constant $C>0$ depending only on $T$, $C_0$, $\Lambda_0$ (not on $\rho$ or $\theta$) such that the principal's value over self-enforcing contracts $V^P_0(\theta;\cdot)$ of (2.25) is well defined on $[0,T]$ and satisfies
--   $$|V^P_0(\theta;s)-V^P_0(\theta;t)|\le C\sqrt{\rho(|s-t|)},\qquad s,t\in[0,T].$$
--
--   This regularity in the starting time of the contract is inherited by the new-hire value $\overline u_0$ (Lemma 3.6), which is the boundary datum of the one-quitting problem.
--
--   **Formalization Note.** The statement also asserts that for every $t\in[0,T]$ the set of values in (2.25) is nonempty and bounded above, so that $V^P_0(\theta;t)$ is a genuine supremum; the paper presupposes this. $C$ is chosen before the model.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Proposition 2.8, (2.26), p. 12

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

theorem proposition_2_8 : ∀ (T : ℝ≥0) (C₀ Λ₀ : ℝ), ∃ C : ℝ, 0 < C ∧
    ∀ {Θ : Type} [MeasurableSpace Θ] (M : Model Θ),
      M.T = T → M.C₀ = C₀ → M.Λ₀ = Λ₀ → M.A22 → M.A27 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ),
      (∀ t ∈ Icc (0 : ℝ) M.T,
        (M.valSet0 S θ t.toNNReal).Nonempty ∧ BddAbove (M.valSet0 S θ t.toNNReal)) ∧
      ∀ s ∈ Icc (0 : ℝ) M.T, ∀ t ∈ Icc (0 : ℝ) M.T,
        |M.V0P S θ s - M.V0P S θ t| ≤ C * Real.sqrt (M.ρ |s - t|) := by sorry

end DynPrincipalAgent.HJB
