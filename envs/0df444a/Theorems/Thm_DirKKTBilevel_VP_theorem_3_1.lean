-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_theorem_3_1
-- name    : DirKKTBilevel.VP.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:25.316717+00:00
-- url     : https://prove2.me/theorems/38d31c7c-02fe-49f9-9856-c256453f4242
-- title:
--   Theorem 3.1, p. 9 — directional KKT condition for (P) under directional calmness
-- statement:
--   Let $X$ be a finite-dimensional real inner product space, and consider
--   $$\text{(P)}\qquad \min_z\ \varphi(z)\quad\text{s.t.}\quad \phi(z)\le0,$$
--   with $\varphi:X\to\mathbb R$ and $\phi:X\to\mathbb R^q$. Let $\bar z$ be a local minimizer of (P). Suppose that
--
--   1. $\varphi$ is continuously differentiable at $\bar z$;
--   2. $\phi$ is directionally Lipschitz and directionally differentiable at $\bar z$ in direction $u$, with directional derivative $\phi'(\bar z;u)$;
--   3. $u\in C(\bar z)$, i.e. $\phi_j'(\bar z;u)\le0$ for every active $j$ and $\nabla\varphi(\bar z)u\le0$;
--   4. (P) is calm at $\bar z$ in direction $u$.
--
--   Then there is $\lambda\in\mathbb R^q$ with $0\le\lambda\perp\phi(\bar z)$, $\lambda\perp\phi'(\bar z;u)$, and
--   $$0\in\nabla\varphi(\bar z)+\partial\langle\lambda,\phi\rangle(\bar z;u),$$
--   where $\partial(\cdot)(\bar z;u)$ is the directional limiting subdifferential of Definition 2.6.
--
--   This is the paper's general directional KKT theorem; Theorem 5.1 is its application to the value-function reformulation of a bilevel program.
--
--   **Formalization Note** The paper states the result on $\mathbb R^n$; here $X$ is any finite-dimensional real inner product space, which is linearly isometric to some $\mathbb R^n$, so nothing is gained or lost. It lets Theorem 5.1 apply this result on the Euclidean product $\mathbb R^n\times\mathbb R^m$. "Continuously differentiable at $\bar z$" is `ContDiffAt ℝ 1`. The orthogonality relations are inner products, $\sum_j\lambda_j\phi_j(\bar z)=0$ and $\sum_j\lambda_j\phi_j'(\bar z;u)=0$. The direction $u$ is not required to be nonzero, as in the paper.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 9, Theorem 3.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Theorem 3.1, p. 9: let `z` be a local minimizer of (P) `min obj` s.t. `con ≤ 0`, with `obj`
continuously differentiable at `z`, `con` directionally Lipschitz and directionally
differentiable at `z` in direction `u` (derivative `d = ϕ'(z; u)`), `u ∈ C(z)`, and (P) calm at
`z` in direction `u`. Then some `λ ∈ ℝ^q` has `0 ≤ λ ⊥ con(z)`, `λ ⊥ d` and
`0 ∈ ∇obj(z) + ∂⟨λ, con⟩(z; u)`. -/
theorem theorem_3_1 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q)
    (hfeas : ∀ j, con z j ≤ 0) (hmin : IsLocalMinOn obj {w | ∀ j, con w j ≤ 0} z)
    (hobj : ContDiffAt ℝ 1 obj z) (hLip : DirLipschitzAt con z u)
    (hdir : HasDirDerivAt con z u d) (hcrit : criticalCone obj con z u d)
    (hcalm : IsCalmDir obj con z u) :
    ∃ l : E q, (∀ j, 0 ≤ l j) ∧ ∑ j, l j * con z j = 0 ∧ ∑ j, l j * d j = 0 ∧
      ∃ ξ ∈ dirSubdiff (fun w => ((∑ j, l j * con w j : ℝ) : EReal)) z u,
        gradient obj z + ξ = 0 := by sorry

end DirKKTBilevel.VP
