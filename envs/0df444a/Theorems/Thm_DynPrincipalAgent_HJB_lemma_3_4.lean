-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_lemma_3_4
-- name    : DynPrincipalAgent.HJB.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:33:26.573689+00:00
-- url     : https://prove2.me/theorems/2015e18d-af92-4184-b1ae-be616a78688e
-- title:
--   Lemma 3.4, p. 14 — an explicit deterministic contract with X_T = 0 and ∫(C₀ − η) ≤ δ under which the agent never quits
-- statement:
--   Let Assumption 2.2 hold. Fix an agent type $\theta$, a time $t<T$ and $\delta>0$. For $x\le\overline L^\theta_t$ and $n\ge1$ consider the deterministic contract (3.6)
--   $$\varepsilon_n=\frac{\overline L^\theta_t-x}{n},\qquad \eta^n_s=I^f\big(\theta;s,f(\theta;s,C_0)-n\big)\mathbf 1_{[t,t+\varepsilon_n)}(s)+C_0\mathbf 1_{[t+\varepsilon_n,T]}(s).$$
--
--   1. For every $x\le\overline L^\theta_t$ and all sufficiently large $n$: $\varepsilon_n<T-t$, $\eta^n\in\mathcal A^P_t$, $(\eta^n,0)\in\mathcal A^\theta_{t,x}$, and
--   $$\int_t^T\big[C_0-\eta^n_s\big]ds\le\delta.$$
--   2. If moreover Assumption 3.1 holds and $\underline L^\theta_t<x\le\overline L^\theta_t$, then for all sufficiently large $n$ the same holds and, in addition, the agent's utility under $(\eta^n,0)$ stays strictly above the lower barrier, $\mathcal X^{\theta;t,x,\eta^n,0}_s>\underline L^\theta_s$ for all $s\in[t,T]$, so that the agent never quits: $\tau^{\theta;t,x,\eta^n,0}=T$.
--
--   The lemma provides the near-optimal, quitting-proof contracts that the paper uses to show that value sets are nonempty and to bound value functions from below.
--
--   **Formalization Note.** The paper's (ii) also says that $(\mathcal X,0,0)$ solves the reflected BSDE (3.3); that clause is not formalized (the mission works in forward form only). The printed "$\mathcal X_s>\overline L^\theta_s$" is a typo for $\underline L^\theta_s$ (the proof shows $\mathcal X\ge\underline L$, and $\mathcal X\le\overline L$ always). The paper's "for some $n$ sufficiently large" is stated as "for every $n\ge N$". The integral bound is stated together with integrability of $C_0-\eta^n$ on $[t,T]$, and the path properties hold almost surely for every continuous version of the (zero) Itô integral.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Lemma 3.4, (3.5)–(3.6), p. 14

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

theorem lemma_3_4 {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (hM : M.A22)
    {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ) (t : ℝ≥0) (ht : t < M.T)
    (δ : ℝ) (hδ : 0 < δ) :
    (∀ x : ℝ, x ≤ M.Lbar θ t → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n ∧ (M.Lbar θ t - x) / n < (M.T : ℝ) - t ∧
      M.IsAP S t (fun s _ => M.eta36 θ t x n s) ∧
      M.InA S θ t x (fun s _ => M.eta36 θ t x n s) (fun _ _ => 0) ∧
      IntegrableOn (fun s => M.C₀ - M.eta36 θ t x n s) (Icc (t : ℝ) M.T) ∧
      ∫ s in Icc (t : ℝ) M.T, (M.C₀ - M.eta36 θ t x n s) ≤ δ) ∧
    (M.A31 → ∀ x : ℝ, M.Lund θ t < x → x ≤ M.Lbar θ t → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n ∧ (M.Lbar θ t - x) / n < (M.T : ℝ) - t ∧
      M.IsAP S t (fun s _ => M.eta36 θ t x n s) ∧
      M.InA S θ t x (fun s _ => M.eta36 θ t x n s) (fun _ _ => 0) ∧
      IntegrableOn (fun s => M.C₀ - M.eta36 θ t x n s) (Icc (t : ℝ) M.T) ∧
      ∫ s in Icc (t : ℝ) M.T, (M.C₀ - M.eta36 θ t x n s) ≤ δ ∧
      ∀ J : ℝ≥0 → Ω → ℝ, M.IsStochInt S t (fun _ _ => 0) J →
        ∀ᵐ ω ∂S.P,
          (∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
            M.Lund θ s < M.fwd θ t x (fun r _ => M.eta36 θ t x n r) (fun _ _ => 0) J s ω) ∧
          M.hitTime θ t x (fun r _ => M.eta36 θ t x n r) (fun _ _ => 0) J ω = M.T) := by sorry

end DynPrincipalAgent.HJB
