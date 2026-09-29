-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_max_function_generalized_gradient
-- name    : ClarkeGradients.MaxFunctions.max_function_generalized_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:45:33.834536+00:00
-- url     : https://prove2.me/theorems/fca7d72b-1963-4fd4-8bce-11b16a564a92
-- title:
--   Theorem (2.1) — generalized gradient and directional derivative of a max function
-- statement:
--   Let $U$ be a nonempty sequentially compact topological space, and let $g:\mathbb R^n\times U\to\mathbb R$ have the following properties:
--
--   - **(a)** $g(x,u)$ is upper semicontinuous in $(x,u)$;
--   - **(b)** $g$ is locally Lipschitz in $x$, uniformly for $u$ in $U$: for each bounded $B\subseteq\mathbb R^n$ there is one $K$ with $|g(x_1,u)-g(x_2,u)|\le K|x_1-x_2|$ for all $x_1,x_2\in B$, $u\in U$;
--   - **(c)** $g^\circ_x(x,u;\cdot)=g'_x(x,u;\cdot)$, the derivatives being with respect to $x$: for all $x,u,v$ the one-sided directional derivative of $y\mapsto g(y,u)$ at $x$ in direction $v$ exists and equals the generalized directional derivative;
--   - **(d)** $\partial_x g(x,u)$ is upper semicontinuous in $(x,u)$: if $(x_i,u_i)\to(x,u)$, $\zeta_i\to\zeta$ and $\zeta_i\in\partial_x g(x_i,u_i)$ for all $i$, then $\zeta\in\partial_x g(x,u)$.
--
--   Let $f(x)=\max\{g(x,u):u\in U\}$ and $M(x)=\{u\in U:\ g(x,u)=f(x)\}$. Then
--
--   1. $f$ is locally Lipschitz;
--   2. for all $x,v$ the one-sided directional derivative $f'(x;v)$ exists;
--   3. $f'(x;v)=f^\circ(x;v)=\max\{\zeta\cdot v:\ \zeta\in\partial_x g(x,u),\ u\in M(x)\}$;
--   4. for all $x$,
--
--   $$
--   \partial f(x)=\operatorname{co}\{\partial_x g(x,u):\ u\in M(x)\}.
--   $$
--
--   This is the paper's first main theorem. It computes the generalized gradient and the directional derivatives of a pointwise maximum of a family of nonsmooth functions. When $\nabla_x g$ exists and is continuous in $(x,u)$, it reduces to Danskin's theorem.
--
--   **Formalization Note** $U\neq\emptyset$ is made explicit (`[Nonempty U]`); the paper uses it implicitly in "max". The max is `⨆ u, g x u`, and "max" in (3) is `IsGreatest`, which asserts attainment. Conclusions (2) and (3) together are "`f` has one-sided directional derivative $f^\circ(x;v)$ at $x$ in direction $v$" plus the `IsGreatest` clause. Upper semicontinuity in (a) is Mathlib's `UpperSemicontinuous` on the product topology; in (d) it is the paper's sequential closed-graph property.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 251, Theorem (2.1)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1). Let `U` be a (nonempty) sequentially compact space and
`g : ℝⁿ × U → ℝ` satisfy
(a) `g` is upper semicontinuous in `(x, u)`;
(b) `g` is locally Lipschitz in `x`, uniformly for `u ∈ U`;
(c) `g°ₓ(x, u; ·) = g'ₓ(x, u; ·)` (the one-sided derivative in `x` exists and equals the
    generalized directional derivative in `x`), for all `x, u`;
(d) `(x, u) ↦ ∂ₓg(x, u)` is upper semicontinuous (sequential closed graph).
Then, with `f(x) = max_u g(x, u)` and `M(x) = {u : g(x, u) = f(x)}`:
(1) `f` is locally Lipschitz; (2) `f'(x; v)` exists; (3)
`f'(x; v) = f°(x; v) = max {ζ · v : ζ ∈ ∂ₓg(x, u), u ∈ M(x)}`; (4) `∂f(x)` is the convex
hull of `{∂ₓg(x, u) : u ∈ M(x)}`. -/
theorem max_function_generalized_gradient
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : U) (v : EuclideanSpace ℝ (Fin n)),
      HasOneSidedDirDeriv (fun y => g y u) x v (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : EuclideanSpace ℝ (Fin n) × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) :
    Shared.LipschitzOnBounded (maxFunction g) ∧
    (∀ x v : EuclideanSpace ℝ (Fin n),
      HasOneSidedDirDeriv (maxFunction g) x v (Shared.genDirDeriv (maxFunction g) x v) ∧
      IsGreatest {r : ℝ | ∃ u ∈ maximizers g x, ∃ ζ ∈ Shared.generalizedGradient (fun y => g y u) x,
          r = inner ℝ ζ v}
        (Shared.genDirDeriv (maxFunction g) x v)) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      Shared.generalizedGradient (maxFunction g) x =
        convexHull ℝ (⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x)) := by sorry

end ClarkeGradients.MaxFunctions
