-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_theorem_3_3
-- name    : BoxTDIMinMax.Separable.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:43.785757+00:00
-- url     : https://prove2.me/theorems/3031ac40-34aa-4fa2-88f9-6c696c4741b0
-- title:
--   Theorem 3.3, p. 14 — min-max formula (3.14) for a separable discrete convex Φ over the integral points of a box-TDI polyhedron
-- statement:
--   Let $\varphi_s:\mathbb Z\to\mathbb Z\cup\{+\infty\}$ be discrete convex for each $s\in S$ and let $\Phi(z)=\sum_{s\in S}\varphi_s(z(s))$. Let $Q\in\mathbb Z^{I\times S}$ and $p\in\mathbb Z^I$ be such that $Qx\ge p$ is box-TDI, its set of integral points $\ddot R$ is nonempty, and $\Phi$ is finite-valued on $\ddot R$. Then:
--   1. $\Phi$ is bounded from below on $\ddot R$ if and only if there exist $z\in\ddot R$ and an integral vector $y\ge 0$ such that $(z,y)$ is $\Phi$-compatible with respect to $Q$;
--   2. if $\Phi$ is bounded from below on $\ddot R$, then
--   $$\min\{\Phi(z) : z\in\ddot R\}=\max\{\Phi(z)-y(Qz-p) : z\in\ddot R,\ y\ge 0 \text{ integer-valued},\ (z,y)\ \Phi\text{-compatible}\}, \qquad (3.14)$$
--   with both the minimum and the maximum attained;
--   3. an optimal $y^*$ in (3.14) can be chosen with at most $2|S|$ positive components.
--
--   This is the paper's main min-max theorem. For linear $\Phi(z)=cz$ it reduces to integral linear programming duality over a box-TDI polyhedron, and for M-convex and M$_2$-convex sets it yields the earlier min-max theorems of Frank and Murota.
--
--   **Formalization Note** "Bounded from below" is the existence of an integer lower bound. The minimum and the maximum are expressed as the least and the greatest element of the respective value sets in $\mathbb Z\cup\{+\infty\}$, equal to one integer $v$; the third clause asks for a maximizing pair $(z,y^*)$ with $\#\{i : y^*(i)>0\}\le 2|S|$. The hypothesis "non-empty integral (box-TDI) polyhedron" is used as $\ddot R\neq\emptyset$; integrality of $R$ is not assumed separately.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 14, Theorem 3.3, (3.14)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Theorem 3.3, p. 14: the min-max formula (3.14) for a separable discrete convex `Φ` over the
integral points `R̈` of a box-TDI polyhedron `R = {x : Q x ≥ p}` (integral `Q`, `p`, `R̈ ≠ ∅`,
`Φ` finite on `R̈`):
1. `Φ` is bounded from below on `R̈` iff there are `z ∈ R̈` and an integral `y ≥ 0` with `(z, y)`
   Φ-compatible;
2. if `Φ` is bounded from below on `R̈`, then
   `min {Φ(z) : z ∈ R̈} = max {Φ(z) - y(Q z - p) : z ∈ R̈, y ≥ 0 integral, (z, y) Φ-compatible}`,
   both attained;
3. the maximum is attained by a pair `(z, y*)` with at most `2|S|` positive components of `y*`. -/
theorem theorem_3_3 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (phi : S → ℤ → WithTop ℤ) (hphi : ∀ s, DiscConvex (phi s))
    (Q : Matrix ι S ℤ) (p : ι → ℤ)
    (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (hne : (intPts Q p).Nonempty)
    (hfin : ∀ z ∈ intPts Q p, Phi phi z ≠ ⊤) :
    ((∃ M : ℤ, ∀ z ∈ intPts Q p, (M : WithTop ℤ) ≤ Phi phi z) ↔
        ∃ z ∈ intPts Q p, ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q z y) ∧
      ((∃ M : ℤ, ∀ z ∈ intPts Q p, (M : WithTop ℤ) ≤ Phi phi z) →
        ∃ v : ℤ,
          IsLeast {w | ∃ z ∈ intPts Q p, w = Phi phi z} (v : WithTop ℤ) ∧
          IsGreatest {w | ∃ z ∈ intPts Q p, ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q z y ∧
              w = Phi phi z + ((-(y ⬝ᵥ (Q *ᵥ z - p)) : ℤ) : WithTop ℤ)} (v : WithTop ℤ) ∧
          ∃ z ∈ intPts Q p, ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q z y ∧
            Phi phi z + ((-(y ⬝ᵥ (Q *ᵥ z - p)) : ℤ) : WithTop ℤ) = (v : WithTop ℤ) ∧
            (Finset.univ.filter (fun i => 0 < y i)).card ≤ 2 * Fintype.card S) := by sorry

end BoxTDIMinMax.Separable
