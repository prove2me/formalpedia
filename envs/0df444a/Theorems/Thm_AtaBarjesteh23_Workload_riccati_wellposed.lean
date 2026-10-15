-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_riccati_wellposed
-- name    : AtaBarjesteh23.Workload.riccati_wellposed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:27.882483+00:00
-- url     : https://prove2.me/theorems/de818fec-b9a2-49f9-83e4-d198a2d47ef0
-- title:
--   §6.3, p. 19 — (50)–(51) and (52)–(53) have at most one C¹ solution; solutions exist on an initial interval of γ ≥ 0 containing 0
-- statement:
--   Assume the standing assumptions. For the Riccati problems (50)–(51) on $[l_\gamma,0]$ and (52)–(53) on $[0,u_\gamma]$ (see the `Setting` file):
--
--   1. for each $\gamma\ge0$, any two continuously differentiable solutions of (50)–(51) agree on $[l_\gamma,0]$, and any two solutions of (52)–(53) agree on $[0,u_\gamma]$;
--   2. $0\in\Gamma^-$ and $0\in\Gamma^+$, i.e. both problems are solvable at $\gamma=0$;
--   3. $\Gamma^-$ and $\Gamma^+$ are order-connected; being subsets of $[0,\infty)$ containing $0$, they are initial intervals of $[0,\infty)$.
--
--   This makes $v^-_\gamma$ and $v^+_\gamma$ well defined on their intervals for $\gamma$ in $\Gamma^-$, resp. $\Gamma^+$, which is what Lemma 4 and Corollary 1 need.
--
--   **Formalization Note** The paper asserts that both problems have a unique solution for every $\gamma\ge0$. Uniqueness is true; existence for every $\gamma$ is not: the solutions blow up in finite time, so (50)–(51) is solvable only for $\gamma$ below a threshold, and similarly (52)–(53). The statement poses the true part: uniqueness, solvability at $0$, and that the solvability sets are intervals.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 19, §6.3, after (53)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem riccati_wellposed (M : Model) (hM : M.Standing) :
    (∀ γ, 0 ≤ γ → ∀ v₁ v₂ : ℝ → ℝ, M.SolvesMinus γ v₁ → M.SolvesMinus γ v₂ →
      EqOn v₁ v₂ (Icc (M.lgam γ) 0)) ∧
    (∀ γ, 0 ≤ γ → ∀ v₁ v₂ : ℝ → ℝ, M.SolvesPlus γ v₁ → M.SolvesPlus γ v₂ →
      EqOn v₁ v₂ (Icc 0 (M.ugam γ))) ∧
    (0 : ℝ) ∈ M.GammaMinus ∧ (0 : ℝ) ∈ M.GammaPlus ∧
    M.GammaMinus.OrdConnected ∧ M.GammaPlus.OrdConnected := by sorry

end AtaBarjesteh23.Workload
