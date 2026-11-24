-- Prove2me | Theorems.Thm_Arxiv1302_0161_bie_from_layer_representation
-- name    : Arxiv1302_0161.bie_from_layer_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:23:29.085131+00:00
-- url     : https://prove2.me/theorems/6a4b88e7-107a-43fb-98f4-8333bcd82a3b
-- title:
--   Eqs. (2.2)-(2.4): the combined layer representation of $u^s$ yields $P\varphi=g$
-- statement:
--   Let $k>0$, let $\eta\neq0$ be real, and let $h_\Gamma\in C^2(\mathbb R)$ have compact support. Let $R>0$ with $\Gamma_p\subset B_R$, and let $d\in S_-$. Let $u^s$ solve (DP) with $f=-(u^i+u^r)$. Extend $u^s$ to $\mathbb R^2_-\setminus\overline{B_R}$ by $u^s(x)=-u^s(x^{re})$. Suppose that, for some $\varphi\in C(\partial D_R^-)$,
--
--   $$u^s(x)=(\mathcal D_k\varphi)(x)-i\eta(\mathcal S_k\varphi)(x)\qquad\text{for all }x\in\mathbb R^2\setminus\overline{D_R^-}.$$
--
--   Then:
--
--   1. $P\varphi=g$ on $\partial D_R^-$, with $P$ and $g$ as in (2.3) and (2.4);
--   2. $g\in C(\partial D_R^-)$;
--   3. $P$ is a bounded linear operator on $C(\partial D_R^-)$: it maps continuous functions to continuous functions, it is linear, and $\|P\psi\|_\infty\le C\|\psi\|_\infty$ for a constant $C$.
--
--   This is the derivation of the paper's boundary integral equation. It uses the jump relations of the layer potentials and the right angles at the corners $x_A,x_B$.
--
--   **Formalization Note** The bound $\|P\psi\|_\infty\le C\|\psi\|_\infty$ is written as: $\|P\psi(x)\|\le CM$ for every upper bound $M$ of $|\psi|$ on the curve.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c004; Section 2, eqs. (2.2), (2.3), (2.4), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem bie_from_layer_representation (k : ℝ) (hk : 0 < k) (eta : ℝ) (heta : eta ≠ 0)
    (h : ℝ → ℝ) (hh : IsLocalProfile h) (R : ℝ) (hR : PerturbationInBall h R)
    (d : R2) (hd : IsLowerDir d) (u : R2 → ℂ) (hu : IsDPSolution k h (incData k d) u)
    (phi : R2 → ℂ) (hphi : ContinuousOn phi (bdry h R))
    (hrep : ∀ x, x ∉ lowerClosed h R → reflExt h u x = combinedPot k eta h R phi x) :
    (∀ x ∈ bdry h R, opP k eta h R phi x = gData k d h R x) ∧
    ContinuousOn (gData k d h R) (bdry h R) ∧
    (∀ psi : R2 → ℂ, ContinuousOn psi (bdry h R) →
      ContinuousOn (opP k eta h R psi) (bdry h R)) ∧
    (∀ (psi1 psi2 : R2 → ℂ) (a b : ℂ), ContinuousOn psi1 (bdry h R) →
      ContinuousOn psi2 (bdry h R) → ∀ x ∈ bdry h R,
        opP k eta h R (fun y => a * psi1 y + b * psi2 y) x =
          a * opP k eta h R psi1 x + b * opP k eta h R psi2 x) ∧
    (∃ C : ℝ, ∀ psi : R2 → ℂ, ContinuousOn psi (bdry h R) → ∀ M : ℝ,
      (∀ y ∈ bdry h R, ‖psi y‖ ≤ M) → ∀ x ∈ bdry h R, ‖opP k eta h R psi x‖ ≤ C * M) := by sorry

end Arxiv1302_0161
