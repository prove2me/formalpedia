-- Prove2me | Theorems.Thm_Arxiv1302_0161_uniqueness_countably_many_incident_waves
-- name    : Arxiv1302_0161.uniqueness_countably_many_incident_waves
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:26:40.790923+00:00
-- url     : https://prove2.me/theorems/f0911b32-f6cc-4dfe-90a5-e1b8c1019e73
-- title:
--   Theorem 4.1: uniqueness from far field patterns of countably many incident plane waves
-- statement:
--   Let $k>0$ be fixed, and let $\Gamma_1=\{x_2=h_1(x_1)\}$ and $\Gamma_2=\{x_2=h_2(x_1)\}$ be two locally rough surfaces, with $h_1,h_2\in C^2(\mathbb R)$ of compact support. Let $(d_n)_{n\in\mathbb N}$ be a sequence of pairwise distinct incident directions in $S_-$. For $j=1,2$ let $u_j^s(\cdot,d_n)$ be the solution of (DP) for $\Gamma_j$ with $f=-(u^i+u^r)$ and incident direction $d_n$, and let $u_j^\infty(\cdot,d_n)$ be its far field pattern on $S_+$. If
--
--   $$u_1^\infty(\hat x,d_n)=u_2^\infty(\hat x,d_n)\qquad\text{for all }\hat x\in S_+\text{ and all }n\in\mathbb N,$$
--
--   then $\Gamma_1=\Gamma_2$, that is, $h_1=h_2$.
--
--   **Formalization Note** The paper writes "$d_n\in S_-$ with $n\in\mathbb N$" and does not say that the directions are distinct. The Introduction describes the result as uniqueness from "a countably infinite number of incident plane waves", so the directions are taken pairwise distinct. With a constant sequence the statement would be uniqueness from a single incident wave, which the paper does not claim.
-- source:
--   H. Zhang and B. Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem, arXiv:1302.0161v1 (2013), claim c010; Section 4, Theorem 4.1, PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1302_0161_Basic

open MeasureTheory Filter Topology

namespace Arxiv1302_0161

theorem uniqueness_countably_many_incident_waves (k : ℝ) (hk : 0 < k)
    (h1 h2 : ℝ → ℝ) (hh1 : IsLocalProfile h1) (hh2 : IsLocalProfile h2)
    (d : ℕ → R2) (hd : ∀ n, IsLowerDir (d n)) (hdinj : Function.Injective d)
    (u1 u2 : ℕ → R2 → ℂ) (hu1 : ∀ n, IsDPSolution k h1 (incData k (d n)) (u1 n))
    (hu2 : ∀ n, IsDPSolution k h2 (incData k (d n)) (u2 n))
    (F1 F2 : ℕ → R2 → ℂ) (hF1 : ∀ n, HasFarFieldOn k (u1 n) (F1 n) upperCircle)
    (hF2 : ∀ n, HasFarFieldOn k (u2 n) (F2 n) upperCircle)
    (heq : ∀ n, ∀ xhat ∈ upperCircle, F1 n xhat = F2 n xhat) :
    h1 = h2 := by sorry

end Arxiv1302_0161
