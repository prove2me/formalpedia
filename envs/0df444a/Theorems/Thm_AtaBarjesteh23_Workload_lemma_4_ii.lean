-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_4_ii
-- name    : AtaBarjesteh23.Workload.lemma_4_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:18.154308+00:00
-- url     : https://prove2.me/theorems/bddbf170-c082-41a0-ab0c-a50793657698
-- title:
--   Lemma 4(ii), p. 19 — γ ↦ v⁺_γ(0) is continuous, strictly decreasing, 0 at 0 and unbounded below
-- statement:
--   Assume the standing assumptions. On the set $\Gamma^+$ of $\gamma\ge0$ for which (52)–(53) is solvable, the map $\gamma\mapsto v^+_\gamma(0)$
--
--   1. is continuous;
--   2. is strictly decreasing;
--   3. satisfies $v^+_0(0)=0$;
--   4. is unbounded below.
--
--   Together with Lemma 4(i) this yields the unique $\gamma^\star$ of Corollary 1.
--
--   **Formalization Note** The paper writes $\lim_{\gamma\to\infty}v^+_\gamma(0)=-\infty$. Since $v^+_\gamma$ exists only for $\gamma$ in an initial interval $\Gamma^+$ (finite-time blow-up), this is stated as unboundedness below on $\Gamma^+$.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 19, Lemma 4(ii)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem lemma_4_ii (M : Model) (hM : M.Standing) :
    ContinuousOn (fun γ => M.vPlus γ 0) M.GammaPlus ∧
    StrictAntiOn (fun γ => M.vPlus γ 0) M.GammaPlus ∧
    M.vPlus 0 0 = 0 ∧
    ¬ BddBelow ((fun γ => M.vPlus γ 0) '' M.GammaPlus) := by sorry

end AtaBarjesteh23.Workload
