-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_constTerm_primitive_eq_poly
-- name    : BarvinokCount.ShortFormula.constTerm_primitive_eq_poly
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:29:31.675002+00:00
-- url     : https://prove2.me/theorems/182f66f4-ba56-499c-bae5-5610c3ca260a
-- title:
--   Corollary 4.2 — the constant term R(K, v, c) of a primitive cone is Q_k(x; y)·∏ x_i⁻¹ with deg Q_k ≤ k
-- statement:
--   For every $k\in\mathbb{N}$ there is a polynomial $Q_k(x_1,\dots,x_k;y)$ with rational coefficients and total degree at most $k$ such that the following holds. For every $d$, every primitive $k$-dimensional cone $K\subseteq\mathbb{R}^d$ with primitive generators $u_1,\dots,u_k\in\mathbb{Z}^d$, every $v\in\mathbb{Z}^d$ and every regular point $c\in\mathbb{R}^d$ of $\sigma(K;\cdot)$ (i.e. $\langle c,u_i\rangle\ne0$ for all $i$), the constant term $R(K,v,c)$ of the Laurent expansion of
--   $$t\longmapsto\exp\{t\cdot\langle c,v\rangle\}\cdot\sigma(K;t\cdot c)$$
--   at $t=0$ exists and equals
--   $$Q_k(x_1,\dots,x_k;y)\cdot\prod_{i=1}^k x_i^{-1},\qquad y=\langle c,v\rangle,\quad x_i=\langle c,u_i\rangle .$$
--
--   This is the explicit evaluation step of the algorithm: once a cone is primitive, its contribution to the lattice-point count is a fixed rational function of $k+1$ inner products.
--
--   **Formalization Note** $Q_k$ is a polynomial in the variables indexed by `Option (Fin k)`: `none` is $y$ and `some i` is $x_i$. It is chosen before $d$, the cone, $v$ and $c$, since it depends on $k$ only. "The constant term exists" means the Laurent-constant-term predicate of the definition file holds.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 773, Corollary 4.2

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_sigma

namespace BarvinokCount.ShortFormula

theorem constTerm_primitive_eq_poly (k : ℕ) :
    ∃ Q : MvPolynomial (Option (Fin k)) ℚ, Q.totalDegree ≤ k ∧
      ∀ (d : ℕ) (u : Fin k → Fin d → ℤ), IsPrimitiveGens u →
        ∀ (v : Fin d → ℤ) (c : Fin d → ℝ), IsRegular u c →
          IsLaurentConstTerm
            (fun t => Real.exp (t * (c ⬝ᵥ castVec v)) * sigma u (t • c))
            (MvPolynomial.aeval
                (fun o : Option (Fin k) => o.elim (c ⬝ᵥ castVec v) fun i => c ⬝ᵥ castVec (u i)) Q /
              ∏ i, c ⬝ᵥ castVec (u i)) := by sorry

end BarvinokCount.ShortFormula
