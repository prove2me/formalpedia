-- Prove2me | Theorems.Thm_ExtADMM_StrongCvx_theorem_4_1
-- name    : ExtADMM.StrongCvx.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:24.09553+00:00
-- url     : https://prove2.me/theorems/52010cc0-f870-4dbc-997a-c0b79c1eab5f
-- title:
--   Theorem 4.1, p. 14 — with strongly convex θᵢ the direct extension of ADMM is not necessarily convergent for all β > 0 (diverges on (4.1) at β = 1)
-- statement:
--   **Theorem 4.1.** For the model (1.1) with strongly convex objective functions, the direct extension of ADMM (1.5) is not necessarily convergent for all $\beta>0$.
--
--   Precisely: the strongly convex instance (4.1),
--
--   $$\min\ 0.05x_1^2+0.05x_2^2+0.05x_3^2\quad\text{s.t.}\quad \begin{pmatrix}1&1&1\\1&1&2\\1&2&2\end{pmatrix}\begin{pmatrix}x_1\\x_2\\x_3\end{pmatrix}=0,$$
--
--   satisfies
--
--   1. the standing assumptions of (1.1) (closed convex sets $\mathcal X_i=\mathbb R$, convex $\theta_i$, nonempty solution set);
--   2. each $\theta_i(x)=0.05x^2$ is strongly convex with modulus $1/10$;
--   3. there is a starting point $(x_2^0,x_3^0,\lambda^0)\in\mathbb R\times\mathbb R\times\mathbb R^3$ such that the direct extension of ADMM (1.5) with $\beta=1$ has a run from it, and no run of (1.5) with $\beta=1$ from it converges: the sequence $(x_1^k,x_2^k,x_3^k,\lambda^k)$ has no limit.
--
--   Hence strong convexity of the objective alone does not secure convergence of (1.5); the known convergence results for strongly convex $\theta_i$ need a restriction on $\beta$ that cannot simply be dropped.
--
--   **Formalization Note** "Not necessarily convergent for all $\beta>0$" is read as "it is not the case that (1.5) converges for every $\beta>0$", witnessed by the explicit instance (4.1) at $\beta=1$, the only value the paper computes. The stronger reading "for every $\beta>0$ there is a divergent run" is false for (4.1): the spectral radius of the iteration matrix is below $1$ for small $\beta$ (about $0.86$ at $\beta=0.1$). Strong convexity uses Mathlib's `StrongConvexOn s m f` ($f-\frac m2\|\cdot\|^2$ convex), so $0.05x^2$ has $m=1/10$; on `Fin 1 → ℝ` the norm is $|x|$. "Converges" means convergence in the product topology; the existence of a run is asserted so that the non-convergence clause is not vacuous. The first block $x_1^0$ of a run is never read by (1.5).
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 14, Theorem 4.1 and (4.1)

import Mathlib
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_StrongCvx_Example41

namespace ExtADMM.StrongCvx

open Matrix Filter Topology

/-- Theorem 4.1, p. 14: for the model (1.1) with strongly convex objective, the direct
extension of ADMM (1.5) is not necessarily convergent for all `β > 0`. Witness: the instance
(4.1), whose `θᵢ(x) = 0.05x²` are `(1/10)`-strongly convex, with `β = 1`: there is a starting
point `(x₂⁰, x₃⁰, λ⁰)` from which a run exists and no run converges. -/
theorem theorem_4_1 :
    example41.Standing ∧
    (StrongConvexOn Set.univ (1/10) example41.θ1 ∧ StrongConvexOn Set.univ (1/10) example41.θ2 ∧
      StrongConvexOn Set.univ (1/10) example41.θ3) ∧
    ∃ (x20 x30 : Fin 1 → ℝ) (lam0 : Fin 3 → ℝ),
      (∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
        example41.IsRun15 1 x1 x2 x3 lam ∧ x2 0 = x20 ∧ x3 0 = x30 ∧ lam 0 = lam0) ∧
      ∀ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
        example41.IsRun15 1 x1 x2 x3 lam → x2 0 = x20 → x3 0 = x30 → lam 0 = lam0 →
          ¬ ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w) := by sorry

end ExtADMM.StrongCvx
