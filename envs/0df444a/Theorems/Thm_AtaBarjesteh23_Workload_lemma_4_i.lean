-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_4_i
-- name    : AtaBarjesteh23.Workload.lemma_4_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:14.063173+00:00
-- url     : https://prove2.me/theorems/15890602-7066-42ea-9004-341d44aa7a19
-- title:
--   Lemma 4(i), p. 19 — γ ↦ v⁻_γ(0) is continuous, strictly increasing, negative at 0 and unbounded above
-- statement:
--   Assume the standing assumptions. On the set $\Gamma^-$ of $\gamma\ge0$ for which (50)–(51) is solvable, the map $\gamma\mapsto v^-_\gamma(0)$
--
--   1. is continuous;
--   2. is strictly increasing;
--   3. satisfies $v^-_0(0)<0$;
--   4. is unbounded above.
--
--   Together with Lemma 4(ii) this yields, by the intermediate value theorem, the unique $\gamma^\star$ of Corollary 1.
--
--   **Formalization Note** The paper writes $\lim_{\gamma\to\infty}v^-_\gamma(0)=\infty$. Because $v^-_\gamma$ blows up in finite time, $v^-_\gamma$ exists only for $\gamma$ in an initial interval $\Gamma^-$ of $[0,\infty)$, possibly bounded; the true content of the printed limit for an increasing function on $\Gamma^-$ is that it is unbounded above there, which is what is stated.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 19, Lemma 4(i)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem lemma_4_i (M : Model) (hM : M.Standing) :
    ContinuousOn (fun γ => M.vMinus γ 0) M.GammaMinus ∧
    StrictMonoOn (fun γ => M.vMinus γ 0) M.GammaMinus ∧
    M.vMinus 0 0 < 0 ∧
    ¬ BddAbove ((fun γ => M.vMinus γ 0) '' M.GammaMinus) := by sorry

end AtaBarjesteh23.Workload
