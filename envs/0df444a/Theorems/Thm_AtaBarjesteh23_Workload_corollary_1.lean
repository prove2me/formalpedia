-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_corollary_1
-- name    : AtaBarjesteh23.Workload.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:15.487888+00:00
-- url     : https://prove2.me/theorems/6724af9e-e460-4f32-ba0d-916d6de8e707
-- title:
--   Corollary 1, p. 20 — there is a unique γ⋆ with v⁻_γ⋆(0) = v⁺_γ⋆(0)
-- statement:
--   Assume the standing assumptions. There is exactly one $\gamma$ such that both Riccati problems (50)–(51) and (52)–(53) are solvable at $\gamma$ and
--   $$v^-_{\gamma}(0)=v^+_{\gamma}(0).$$
--   This $\gamma$ is $\gamma^\star$, the optimal long-run average cost of the EWF.
--
--   Corollary 1 is what makes the pasted function $v$ of (54) continuous at $0$, and it determines the barriers $l_{\gamma^\star}$, $u_{\gamma^\star}$.
--
--   **Formalization Note** Uniqueness is among the $\gamma$ at which both sides are defined, i.e. $\gamma\in\Gamma^-\cap\Gamma^+$.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 20, Corollary 1

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

namespace AtaBarjesteh23.Workload

theorem corollary_1 (M : Model) (hM : M.Standing) :
    ∃! γ : ℝ, γ ∈ M.GammaMinus ∧ γ ∈ M.GammaPlus ∧ M.vMinus γ 0 = M.vPlus γ 0 := by sorry

end AtaBarjesteh23.Workload
