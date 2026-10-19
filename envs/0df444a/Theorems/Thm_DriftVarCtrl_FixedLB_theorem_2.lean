-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_theorem_2
-- name    : DriftVarCtrl.FixedLB.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:24.196524+00:00
-- url     : https://prove2.me/theorems/5e953842-4a37-4e3d-94d9-daf432e656c6
-- title:
--   Theorem 2, pp. 12–13 — the optimal policy in each of the regions (7)–(10)
-- statement:
--   Assume $v_1 < v_2$ and let conditions (7)–(10) be as defined from the slopes $d_1^L, d_1^U, d_2^L, d_2^U$.
--   1. If (7) holds, the policy of always using control 1 is optimal.
--   2. If (8) holds, the policy of always using control 2 is optimal.
--   3. If (9) holds, then for some $S^* \in (0,U)$ the two-interval policy using control 1 on $[0,S^*)$ and control 2 on $[S^*,U)$ is optimal.
--   4. If (10) holds, then for some $S^* \in (0,U)$ the two-interval policy using control 2 on $[0,S^*)$ and control 1 on $[S^*,U)$ is optimal.
--
--   Theorem 2 gives an explicit optimal policy in every region of the cost plane $(h_1,h_2)$; with the exhaustiveness of (7)–(10) it yields the existence half of Theorem 1.
--
--   **Formalization Note.** "Optimal" is the mission's `IsOptimal`: the policy has an analytic value lying below the value of every interval policy on $[0,U]$. Only existence of $S^*$ is claimed in parts 3–4. The paper proves (a) and (c) and omits (b) and (d) as similar; all four are stated. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 12–13, Theorem 2 (a)–(d); proof pp. EC-4–EC-7

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants

namespace DriftVarCtrl.FixedLB

/-- Theorem 2 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 12–13). Under the standing `v₁ < v₂`:
(a) if (7) holds, always using control 1 is optimal; (b) if (8) holds, always using control 2 is
optimal; (c) if (9) holds, the two-interval policy using control 1 on `[0, S*)` and control 2 on
`[S*, U)` is optimal for some `S* ∈ (0, U)`; (d) if (10) holds, the two-interval policy using control 2
on `[0, S*)` and control 1 on `[S*, U)` is optimal for some `S* ∈ (0, U)`.

Formalization Note: optimality is `IsOptimal` (analytic value, over all interval policies); only
existence of `S*` is claimed in (c)–(d). The paper omits the proofs of (b) and (d) as similar. -/
theorem theorem_2 (p : Params) (hv : v p .one < v p .two) :
    (cond7 p → IsOptimal p (static p .one)) ∧
    (cond8 p → IsOptimal p (static p .two)) ∧
    (cond9 p → ∃ (S : ℝ) (hS : S ∈ Set.Ioo 0 p.U), IsOptimal p (twoInt p .one S hS)) ∧
    (cond10 p → ∃ (S : ℝ) (hS : S ∈ Set.Ioo 0 p.U), IsOptimal p (twoInt p .two S hS)) := by sorry

end DriftVarCtrl.FixedLB
