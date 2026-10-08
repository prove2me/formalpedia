-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_optimality_4_16
-- name    : BeckTeboulleMD.EMDA.optimality_4_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:34.990582+00:00
-- url     : https://prove2.me/theorems/bb6e9119-c493-44c3-955d-8d4365c5b406
-- title:
--   Proof of Theorem 4.1, (4.16), p. 171 — optimality of the SANP step: ⟨x − x^{k+1}, t_k f′(x^k) + ∇ψ(x^{k+1}) − ∇ψ(x^k)⟩ ≥ 0
-- statement:
--   Let $E$ be a real normed space, $X \subseteq E$ convex, $\psi : E \to \mathbb R$, and let $(x^k)_{k\ge1}$ be a run of SANP (3.11) over $X$ with oracle $f'$ and step sizes $t_k > 0$, that is, $x^{k+1}$ minimises $x \mapsto \langle x, f'(x^k)\rangle + t_k^{-1} B_\psi(x, x^k)$ over $X$ and $\psi$ is differentiable at every iterate. Then for every $k \ge 1$,
--   $$\langle x - x^{k+1},\ t_k f'(x^k) + \nabla\psi(x^{k+1}) - \nabla\psi(x^k)\rangle \ge 0 \qquad \text{for all } x \in X.$$
--   In particular, for $x = x^*$ one obtains $\langle x^* - x^{k+1},\ \nabla\psi(x^k) - \nabla\psi(x^{k+1}) - t_k f'(x^k)\rangle \le 0$, which is (4.16) in the form the proof uses.
--
--   This first-order optimality condition is the first of the three estimates in the proof of Theorem 4.1.
--
--   **Formalization Note** Subgradients and derivatives are continuous linear functionals; $\langle u, \ell\rangle$ is $\ell(u)$. Only convexity of $X$ and the SANP run are assumed: the optimality condition needs differentiability of $\psi$ at $x^{k+1}$ and $x^k$, which the run provides, and not the strong convexity of $\psi$. The page prints (4.16) with "$\ge 0$" after negating the bracket; the proof uses it as $s_1 \le 0$ with $s_1$ the same pairing (4.17), so the printed inequality sign is a slip and is not copied.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 171, proof of Theorem 4.1, optimality condition before (4.16) and (4.16)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Proof of Theorem 4.1, p. 171, the optimality condition of (3.11) preceding (4.16): for a SANP run
over a convex set `X`, for every `k ≥ 1` and every `u ∈ X`,
`⟨u − x^{k+1}, t_k f′(x^k) + ∇ψ(x^{k+1}) − ∇ψ(x^k)⟩ ≥ 0`. -/
theorem optimality_4_16 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ψ : E → ℝ) (g : E → E →L[ℝ] ℝ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → ∀ u ∈ X,
      0 ≤ (t k • g (x k) + fderiv ℝ ψ (x (k + 1)) - fderiv ℝ ψ (x k)) (u - x (k + 1)) := by sorry

end BeckTeboulleMD.EMDA
