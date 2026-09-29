-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_theorem_4_2
-- name    : ChanPangGQVI.Existence.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:41:16.760822+00:00
-- url     : https://prove2.me/theorems/27a356f8-aa07-4899-83fa-cc974b8febf1
-- title:
--   Theorem 4.2 — existence for the generalized implicit complementarity problem GICP(L̃, m, μ + q) under strong copositivity
-- statement:
--   Let $\tilde L$ be a nonempty closed solid convex cone in $\mathbb R^n$ (solid: nonempty interior). Let $m$ be a continuous point-to-point mapping and $\mu$ a point-to-set mapping of $\mathbb R^n$ into itself, and let $K(x)=m(x)+\tilde L$. Assume that
--
--   1. there is a vector $\tilde u\in\mathbb R^n$ with $\tilde u-m(x)\in\tilde L$ for all $x\in\mathbb R^n$;
--   2. $\mu$ is strongly copositive with respect to $K$ at $\tilde u$: there are $\alpha>0$ and $y^0\in\mu(\tilde u)$ with $(y-y^0)^T(x-\tilde u)\ge\alpha\|x-\tilde u\|^2$ for all $x\in K(x)$ and all $y\in\mu(x)$;
--   3. $\mu$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $\mathbb R^n$.
--
--   Then for each vector $q\in\mathbb R^n$ the generalized implicit complementarity problem $\mathrm{GICP}(L,m,\mu+q)$ with $L(x)=\tilde L$ for all $x$ has a solution: there are $x$ and $y$ with
--
--   $$
--   x-m(x)\in\tilde L,\qquad y\in\mu(x)+q,\qquad y\in\tilde L^*,\qquad y^T\big(x-m(x)\big)=0 .
--   $$
--
--   This is the paper's existence theorem for the generalized implicit complementarity problem; it contains existence results for implicit and generalized complementarity problems with strongly monotone data.
--
--   **Formalization Note** $\tilde L$ is a Mathlib `PointedCone`, which is convex and contains $0$, so "nonempty" holds automatically. Semicontinuity on $\mathbb R^n$ is `UpperHemicontinuous`. Note that $K(x)=m(x)+\tilde L$ has closed values because $\tilde L$ is closed, so no implicit closedness hypothesis is needed.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 218, Theorem 4.2 (proof on p. 219)

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_GICP
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet
import Definitions.Def_ChanPangGQVI_Existence_Coercivity

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 218, Theorem 4.2. Let `L̃` be a nonempty closed solid cone in `ℝⁿ`, `m`
a continuous point-to-point and `μ` a point-to-set mapping of `ℝⁿ`, and `K(x) = m(x) + L̃`.
Assume (i) there is `ũ` with `ũ - m(x) ∈ L̃` for all `x`; (ii) `μ` is strongly copositive with
respect to `K` at `ũ`; (iii) `μ` is a nonempty contractible compact valued upper semicontinuous
mapping on `ℝⁿ`. Then for each `q`, `GICP(L, m, μ + q)` with `L(x) = L̃` for all `x` has a solution.

`L̃` is `Lt`, `ũ` is `ut`. A `PointedCone` is convex and contains `0`, so "nonempty" is built in;
"solid" is a nonempty interior. -/
theorem theorem_4_2 {n : ℕ} (Lt : PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (hLt_closed : IsClosed (Lt : Set (EuclideanSpace ℝ (Fin n))))
    (hLt_solid : (interior (Lt : Set (EuclideanSpace ℝ (Fin n)))).Nonempty)
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hm : Continuous m)
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (ut : EuclideanSpace ℝ (Fin n))
    (hi : ∀ x : EuclideanSpace ℝ (Fin n), ut - m x ∈ Lt)
    (hii : IsStronglyCopositiveAt μ (coneTranslate m (fun _ => Lt)) ut)
    (hμ_ne : ∀ x, (μ x).Nonempty) (hμ_contr : ∀ x, IsContractibleSet (μ x))
    (hμ_cpt : ∀ x, IsCompact (μ x)) (hμ_usc : UpperHemicontinuous μ) :
    ∀ q : EuclideanSpace ℝ (Fin n),
      ∃ x y : EuclideanSpace ℝ (Fin n), IsGICPSolution (fun _ => Lt) m (shiftMap μ q) x y := by sorry

end ChanPangGQVI.Existence
