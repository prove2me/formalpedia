-- Prove2me | Theorems.Thm_ChanPangGQVI_Contraction_theorem_5_3
-- name    : ChanPangGQVI.Contraction.theorem_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:05:20.097887+00:00
-- url     : https://prove2.me/theorems/60fde0c8-43ba-4698-abfc-32a7d69fdaa5
-- title:
--   Theorem 5.3 — $F_\lambda(x)=P_{m(x)+\tilde K}(x-\lambda f(x))$ is a contraction whose iterates converge to a GQVI solution
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean norm and inner product. Let $m$ and $f$ be point-to-point mappings of $\mathbb R^n$ into itself and let $\tilde K$ be a nonempty closed convex set in $\mathbb R^n$. Suppose that for all $x$ and $y$
--
--   1. $\|m(x)-m(y)\|\le\alpha\|x-y\|$ and $\|f(x)-f(y)\|\le\beta\|x-y\|$ (Lipschitz continuity with constants $\alpha$, $\beta$);
--   2. $(x-y)^T(f(x)-f(y))\ge\delta\|x-y\|^2$ and $(x-y)^T(m(x)-m(y))\ge\gamma\|x-y\|^2$ (strong monotonicity with constants $\delta$, $\gamma$).
--
--   Put $K(x)=m(x)+\tilde K$ and $F_\lambda(x)=P_{K(x)}(x-\lambda f(x))$, where $P_S(z)$ is the Euclidean projection of $z$ on $S$. Then for each $\lambda>0$ satisfying
--
--   $$
--   \lambda^2\beta^2+2\lambda(\alpha\beta-\delta)-2(\gamma-\alpha)<0,
--   $$
--
--   the following hold:
--
--   1. $F_\lambda$ is a contraction: there is a constant $c<1$ with $\|F_\lambda(x)-F_\lambda(y)\|\le c\|x-y\|$ for all $x,y$;
--   2. $F_\lambda$ has a fixed point $\tilde x_\lambda$;
--   3. $\tilde x_\lambda$ solves $\mathrm{GQVI}(K,f)$, i.e. $\tilde x_\lambda\in K(\tilde x_\lambda)$ and $(x'-\tilde x_\lambda)^T f(\tilde x_\lambda)\ge0$ for all $x'\in K(\tilde x_\lambda)$;
--   4. for every initial vector $x^0\in\mathbb R^n$, the iterates $x^{k+1}=F_\lambda(x^k)$, $k=0,1,2,\dots$, converge to $\tilde x_\lambda$.
--
--   The theorem gives a globally convergent iterative method for a class of quasi-variational inequalities whose feasible set moves by translation, each step being a projection on the fixed set $\tilde K$ (a quadratic program when $\tilde K$ is polyhedral).
--
--   **Formalization Note** The contraction is Mathlib's `ContractingWith c F_λ` with `c : ℝ≥0`, i.e. `c < 1` and `F_λ` Lipschitz with constant `c`, the constant independent of the points. The Lipschitz and monotonicity constants are real numbers with no sign conditions, exactly as in the paper; the GQVI is taken with the singleton-valued mapping $x\mapsto\{f(x)\}$. Uniqueness of the fixed point is not stated separately (it follows from conclusion 4).
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 221, Theorem 5.3

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Definitions.Def_ChanPangGQVI_Contraction_ProjectionMap

open scoped RealInnerProductSpace NNReal Topology
open Filter

namespace ChanPangGQVI.Contraction

/-- **Theorem 5.3** (Chan and Pang 1982, p. 221). Let `m` and `f` be point-to-point mappings of
`ℝⁿ` into itself and `K̃` a nonempty closed convex set in `ℝⁿ`. Suppose `m` and `f` are
Lipschitz continuous with constants `α`, `β` and strongly monotone with constants `γ`, `δ`
(Euclidean norm and inner product). Then for each `λ > 0` with
`λ²β² + 2λ(αβ - δ) - 2(γ - α) < 0`, the mapping `F_λ(x) = P_{K(x)}(x - λ f(x))`, where
`K(x) = m(x) + K̃`, is a contraction (`ContractingWith c F_λ` for a constant `c < 1`), and it has
a fixed point `x̃_λ` which solves `GQVI(K, f)` and is the limit of the iterates
`x^{k+1} = F_λ(x^k)` from every initial vector `x⁰ ∈ ℝⁿ`. -/
theorem theorem_5_3 {n : ℕ}
    (m f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (α β γ δ : ℝ)
    (hm_lip : ∀ x y, ‖m x - m y‖ ≤ α * ‖x - y‖)
    (hf_lip : ∀ x y, ‖f x - f y‖ ≤ β * ‖x - y‖)
    (hf_mono : ∀ x y, δ * ‖x - y‖ ^ 2 ≤ ⟪x - y, f x - f y⟫)
    (hm_mono : ∀ x y, γ * ‖x - y‖ ^ 2 ≤ ⟪x - y, m x - m y⟫)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam_cond : lam ^ 2 * β ^ 2 + 2 * lam * (α * β - δ) - 2 * (γ - α) < 0) :
    (∃ c : ℝ≥0, ContractingWith c (Flam m f Ktil lam)) ∧
      ∃ xt : EuclideanSpace ℝ (Fin n),
        Flam m f Ktil lam xt = xt ∧
        ChanPangGQVI.Shared.IsGQVISolution (Kmap m Ktil) (fun z => {f z}) xt (f xt) ∧
        ∀ x0 : EuclideanSpace ℝ (Fin n),
          Tendsto (fun k : ℕ => (Flam m f Ktil lam)^[k] x0) atTop (𝓝 xt) := by sorry

end ChanPangGQVI.Contraction
