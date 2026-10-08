-- Prove2me | Theorems.Thm_AffinePolicies_Simplex_theorem_1
-- name    : AffinePolicies.Simplex.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:31.244992+00:00
-- url     : https://prove2.me/theorems/3ae0fd1e-6173-4a7f-aea2-7e12dadb375d
-- title:
--   Theorem 1, PDF pp. 5–6 — if 𝒰 is a simplex in ℝ^m_+, some affine policy is optimal for Π_Adapt(𝒰)
-- statement:
--   Consider the two-stage adaptive problem $\Pi_{Adapt}(\mathcal U)$ of model (1),
--   $$z_{Adapt}(\mathcal U)=\min_{x,\,y(\cdot)}\ c^Tx+\max_{b\in\mathcal U}d^Ty(b)\quad\text{s.t. } Ax+By(b)\ge b,\ x\ge 0,\ y(b)\ge 0\ \ \forall b\in\mathcal U,$$
--   with $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$. Suppose the uncertainty set is a simplex,
--   $$\mathcal U=\operatorname{conv}(b^1,\dots,b^{m+1}),$$
--   where $b^1,\dots,b^{m+1}\in\mathbb R^m_+$ are affinely independent, and that the problem is feasible. Then there is an optimal two-stage solution $(\hat x,\hat y)$ whose second stage is an affine function of $b$: there are $P\in\mathbb R^{n_2\times m}$ and $q\in\mathbb R^{n_2}$ with
--   $$\hat y(b)=Pb+q\qquad\text{for all } b\in\mathcal U,$$
--   and $(\hat x,\hat y)$ is optimal among **all** (not only affine) two-stage solutions. In particular $z_{Aff}(\mathcal U)=z_{Adapt}(\mathcal U)$.
--
--   The result marks the boundary of exactness for affine policies: Sections 3 and 4 of the paper show that already for sets with $m+3$ extreme points affine policies can be suboptimal, and that the gap can grow like $m^{1/2-\delta}$.
--
--   **Formalization Note** "Optimal" means: $(\hat x,\hat y)$ is feasible, and every worst-case cost bound achieved by some feasible two-stage solution is also achieved by $(\hat x,\hat y)$; this asserts that the minimum in (1) is attained (the paper's proof presupposes an optimal solution). The page writes "$b^j\in\mathbb R^m_+$ for all $j=1,\dots,m$"; all $m+1$ vertices are required nonnegative, as $\mathcal U\subseteq\mathbb R^m_+$ in (1) demands. The simplex is automatically compact, convex and (by affine independence) full-dimensional, so these standing assumptions of (1) are not stated separately. Feasibility is the paper's standing assumption on (1). Vertices are indexed from $0$: $b^j$ is `v (j-1)`.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 1, PDF pp. 5–6

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.Simplex

theorem theorem_1 {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v) (hvnn : ∀ j, 0 ≤ v j)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
      Feasible A B (simplexSet v) x y) :
    ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
      IsOptimalAdapt A B c d (simplexSet v) x (affinePolicy P q) := by sorry

end AffinePolicies.Simplex
