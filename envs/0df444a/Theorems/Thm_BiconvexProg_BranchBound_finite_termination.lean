-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_finite_termination
-- name    : BiconvexProg.BranchBound.finite_termination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:57:39.921361+00:00
-- url     : https://prove2.me/theorems/d8aaac0d-29a4-460c-a4c5-282b9ab70d4d
-- title:
--   Finite termination — if $v_b^k = V_b^k$, the stage point attaining $V_b^k$ solves Problem $\mathcal P$
-- statement:
--   Let $S, f, g, \Omega$ satisfy the standing hypotheses of Problem $\mathcal P$, and consider any run of the branch-and-bound algorithm. Suppose that at some stage $k$ the best bounds coincide, $v_b^k = V_b^k$, and let $l \le k$ be a stage whose point attains the best upper bound, $\varphi(x^l, y^l) = V_b^k$. Then $(x^l, y^l) \in S \cap \Omega$ and
--
--   $$\varphi(x^l, y^l) \le \varphi(x, y) \qquad \text{for all } (x, y) \in S \cap \Omega,$$
--
--   so $(x^l, y^l)$ is a global solution of Problem $\mathcal P$.
--
--   This is the algorithm's stopping test. The paper states it at Stage 2 ("If $v_b^2 = V_b^2$, we are done") and uses it at every stage.
--
--   **Formalization Note** The paper's remark is made at Stage 2 and generalized here to an arbitrary stage, as the algorithm's description implies.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 278, remark after the Stage 2 bound chain

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

/-- Finite termination (p. 278, stated there for stage 2): if at some stage the best lower and
upper bounds coincide, `v_bᵏ = V_bᵏ`, then every earlier stage point `(xˡ, yˡ)`, `l ≤ k`, that
attains `V_bᵏ` is a global solution of Problem 𝒫. -/
theorem finite_termination {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (k l : ℕ) (hl : l ≤ k) (hVl : objective f g (pt l) = bestUpper f g pt k)
    (heq : bestLower f g sel pt k = bestUpper f g pt k) :
    pt l ∈ S ∩ Ω.toSet ∧ IsMinOn (objective f g) (S ∩ Ω.toSet) (pt l) := by sorry

end BiconvexProg.BranchBound
