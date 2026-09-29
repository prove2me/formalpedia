-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_limit_identity
-- name    : BiconvexProg.BranchBound.limit_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T17:59:10.391393+00:00
-- url     : https://prove2.me/theorems/e7d72335-3a48-4df8-be82-3431b167e0fe
-- title:
--   The limit identity — along a convergent subsequence of stage points, $\psi^{k_t}(x^{k_t},y^{k_t}) \to \varphi(\bar x, \bar y)$
-- statement:
--   Let $S, f, g, \Omega$ satisfy the standing hypotheses of Problem $\mathcal P$, and consider any run of the branch-and-bound algorithm, with stage points $(x^k, y^k)$ and best lower bounds $v_b^k = \psi^{k}(x^k, y^k)$. If a subsequence $(x^{k_t}, y^{k_t})$, $t = 1, 2, \dots$, converges to $(\bar x, \bar y)$, then
--
--   $$\lim_{t \to \infty} \psi^{k_t}(x^{k_t}, y^{k_t}) = \varphi(\bar x, \bar y).$$
--
--   This is the key step of the convergence proof. At an accumulation point the underestimates become exact, which forces $\varphi(\bar x, \bar y) \le v^*$.
--
--   **Formalization Note** The paper writes the identity with $f$ and $g$ dropped, as $\bar\psi(\bar x,\bar y) = \lim_t \mathrm{Vex}_{\Omega^{k(t)}} x^{k_t} \cdot y^{k_t} = \varphi(\bar x,\bar y)$, along a nested subsequence it constructs. It is stated here with $f$ and $g$ included and for every convergent subsequence: from any subsequence the paper's construction extracts a nested one. The value $\psi^{k_t}(x^{k_t}, y^{k_t})$ is taken as the selected node's value $\psi^{B_{k_t}}(x^{k_t}, y^{k_t}) = v_b^{k_t}$. The paper's own argument for the existence of the limit goes through the equicontinuity of $\{\psi^k\}$, which fails (see the equicontinuity item). The statement itself is the paper's claim.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 280, Convergence proof (last display)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

open Filter Topology

/-- The limit identity (p. 280, last display): along a run, if a subsequence `(x^{k_t}, y^{k_t})` of
stage points converges to `(x̄, ȳ)`, then the stage values `ψ^{k_t}(x^{k_t}, y^{k_t}) = v_b^{k_t}`
converge to `φ(x̄, ȳ)`. -/
theorem limit_identity {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (φs : ℕ → ℕ) (hφs : StrictMono φs) (zbar : (Fin n → ℝ) × (Fin n → ℝ))
    (hconv : Tendsto (fun t => pt (φs t)) atTop (𝓝 zbar)) :
    Tendsto (fun t => bestLower f g sel pt (φs t)) atTop (𝓝 (objective f g zbar)) := by sorry

end BiconvexProg.BranchBound
