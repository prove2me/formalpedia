-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_stage_fun_mono
-- name    : BiconvexProg.BranchBound.stage_fun_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:56:25.800287+00:00
-- url     : https://prove2.me/theorems/633ff535-6f18-41f9-9207-1016fd4ce662
-- title:
--   Convergence proof — the stage functions are piecewise convex, increase, stay below $\varphi$ on $\Omega$, and converge pointwise to $\bar\psi \le \varphi$
-- statement:
--   Let $S, f, g, \Omega$ satisfy the standing hypotheses of Problem $\mathcal P$, and consider any run of the convex-envelope branch-and-bound algorithm, with open nodes $\mathcal N_k$ and stage functions $\psi^k(z) = \min\{\psi^B(z) : B \in \mathcal N_k,\ z \in B\}$. Then $\psi^k$ is piecewise convex: every open node function $\psi^B(x,y) = f(x) + \mathrm{Vex}_B\, x^\top y + g(y)$, $B \in \mathcal N_k$, is convex on its box $B$. Moreover, for every $(x,y) \in \Omega$ and every stage $k$,
--
--   $$\psi^k(x,y) \le \psi^{k+1}(x,y) \le \varphi(x,y),$$
--
--   and consequently the limit $\bar\psi(x,y) = \lim_{k\to\infty} \psi^k(x,y)$ exists and satisfies $\bar\psi(x,y) \le \varphi(x,y)$.
--
--   These inequalities open the paper's convergence proof. The underestimates only improve as the tree grows, and the limit function $\bar\psi$ is the object the proof compares with $\varphi$ at accumulation points.
--
--   **Formalization Note** The paper also asserts that $\psi^k$ is continuous over $\Omega$. That is false in general: from stage 3 on, the node functions of two open boxes can differ at a shared point, and the stage function jumps there (see the mission notes). The piecewise convexity (convexity of each open node function on its box), the inequalities and the pointwise convergence are formalized. The stage function takes the minimum over the open boxes containing the point, which agrees with the paper's definition wherever that definition is unambiguous.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 279, Convergence proof (first two displays)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

open Filter Topology

/-- Convergence proof, p. 279: along a run, the stage functions are piecewise convex (each open
node function `ψ^B` is convex on its box `B`), underestimate `φ` on `Ω`, increase from stage to
stage, and hence converge pointwise on `Ω` to a limit `ψ̄ ≤ φ`. -/
theorem stage_fun_mono {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    (∀ k, ∀ B ∈ nodes k, ConvexOn ℝ B.toSet (nodeFun f g B)) ∧
    (∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ objective f g z) ∧
    (∀ k, ∀ z ∈ Ω.toSet, stageFun f g (nodes k) z ≤ stageFun f g (nodes (k + 1)) z) ∧
    (∀ z ∈ Ω.toSet, ∃ ψbar : ℝ,
      Tendsto (fun k => stageFun f g (nodes k) z) atTop (𝓝 ψbar) ∧ ψbar ≤ objective f g z) := by sorry

end BiconvexProg.BranchBound
