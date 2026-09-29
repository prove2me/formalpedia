-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_node_envelope_equicontinuous
-- name    : BiconvexProg.BranchBound.node_envelope_equicontinuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T17:58:46.736335+00:00
-- url     : https://prove2.me/theorems/c280d716-4ac1-4f1b-8576-bc7edc7de98d
-- title:
--   Equicontinuity estimate (corrected) — $\|z-w\| < \varepsilon/(n\gamma) \Rightarrow |\mathrm{Vex}_B x^\top y(z) - \mathrm{Vex}_B x^\top y(w)| < \varepsilon$ within every sub-box $B$
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n \times \mathbb{R}^n$ be a nonempty box, let $\gamma_i$ be the maximum gradient norm of $x_i y_i$ over its rectangle $\Omega_i$, and let $\gamma = \max_i \gamma_i$. For every sub-box $B$ of $\Omega$, every $\varepsilon > 0$ and all $z, w \in B$,
--
--   $$n\,\gamma\, \|z - w\| < \varepsilon \ \Longrightarrow\ \big|\mathrm{Vex}_B\, x^\top y\,(z) - \mathrm{Vex}_B\, x^\top y\,(w)\big| < \varepsilon ,$$
--
--   where $\|\cdot\|$ is the Euclidean norm of $\mathbb{R}^{2n}$. For $\gamma > 0$ this is the paper's choice $\delta = \varepsilon/(n\gamma)$. In the convergence proof's reduced setting ($f$ and $g$ dropped), $\mathrm{Vex}_B\, x^\top y$ is the node function of $B$. The estimate is therefore uniform over all nodes of all stages.
--
--   **Formalization Note** This corrects the paper's chain in two places. (i) The intermediate display $|H_i^{kj}(x_i,y_i) - H_i^{kj}(u_i,v_i)| \le |x_i y_i - u_i v_i|$ on p. 282 is false: on $[0,2]^2$ the points $(1,1)$ and $(1+a, 1/(1+a))$ give $0$ on the right and $2a^2/(1+a) > 0$ on the left. It is not formalized; the bound goes through the Lipschitz constant $\gamma_i$ instead. (ii) The chain concludes $|\psi^k(z) - \psi^k(w)| < \varepsilon$ for the stage function on all of $\Omega$, which is false. From stage 3 on, the stage function can jump across a face shared by two open boxes, so the family $\{\psi^k\}$ is not equicontinuous. What the chain establishes, and what is formalized, is the estimate within each box. The condition is written as $n\gamma\|z-w\| < \varepsilon$ to avoid dividing by $\gamma = 0$, the case in which $\Omega$ is a single point.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, pp. 281–282, Convergence proof (cone argument and final implication chain; corrected)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem
import Definitions.Def_BiconvexProg_BranchBound_gradNormMax

namespace BiconvexProg.BranchBound

/-- Equicontinuity estimate of p. 282, corrected to hold within each box. Let `γ = maxᵢ γᵢ`, with
`γᵢ` the maximum gradient norm of `xᵢyᵢ` over the rectangle `Ωᵢ`. For every sub-box `B` of `Ω`,
every `ε > 0` and all `z, w ∈ B` with `n γ ‖z − w‖ < ε` (Euclidean norm on `ℝ²ⁿ`, i.e. the
paper's `δ = ε/(nγ)`), the reduced node functions satisfy
`|Vex_B xᵀy (z) − Vex_B xᵀy (w)| < ε`. -/
theorem node_envelope_equicontinuous {n : ℕ} (Ω : Box n) (hlL : Ω.l ≤ Ω.L) (hmM : Ω.m ≤ Ω.M)
    (B : Box n) (hB : B.IsSubBox Ω) (ε : ℝ) (hε : 0 < ε)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ B.toSet) (hw : w ∈ B.toSet)
    (hδ : (n : ℝ) * (⨆ i, gradNormMax (Ω.l i) (Ω.L i) (Ω.m i) (Ω.M i)) * eucDist z w < ε) :
    |convexEnvelope B.toSet bilin z - convexEnvelope B.toSet bilin w| < ε := by sorry

end BiconvexProg.BranchBound
