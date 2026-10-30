-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_curve_isotopy
-- name    : ContactTopology.equivariant_legendrian_core_curve_isotopy
-- status  : Open
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:55:49.620653+00:00
-- url     : https://prove2.me/theorems/c5e12582-0450-4422-b48c-37310a1b3b02
-- title:
--   Legendrian curve isotopy for a contactomorphic standard core
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere that commutes with the antipodal involution. For $u=(u_1,u_2)\in S^1$, put $c(u)=(u_1,u_2,0,0)$. There is a smooth parametrized antipodally equivariant Legendrian isotopy $k_t:S^1\to S^3$ with
--   $$k_0(u)=F(c(u)),\qquad k_1(u)=c(u).$$
--   Every slice for $0\le t\le1$ is injective with nonzero circle tangent derivative. The family has a globally smooth ambient representative $k:\mathbb R\times\mathbb R^2\to\mathbb R^4$, and for every real $t$ its restriction to $S^1$ lies in the sphere, obeys $k_t(-u)=-k_t(u)$, and is Legendrian:
--   $$\lambda_{k_t(u)}\bigl(Dk_{(t,u)}(0,Ju)\bigr)=0,\qquad Ju=(-u_2,u_1).$$
--
--   This is the standard $\mathbb{RP}^3=L(2,1)$ rational-Legendrian-unknot classification input, expressed on its sphere cover with endpoint parametrizations fixed. It asserts an isotopy of the curves themselves. A separate Legendrian isotopy-extension theorem turns this family into an ambient contact isotopy.
--
--   **Formalization Note.** The all-real-time sphere, symmetry and Legendrian conditions describe a smooth extension beyond the closed unit time interval. No injectivity or immersion condition is imposed outside that interval.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Theorem 1.5 (printed p. 4), Proposition 3.5 (printed pp. 31–32), and Section 4 proof of Theorem 1.1 (Claim 1 and p=2 case, printed pp. 32–33). Also uses smooth L(2,1) mapping-class triviality in Theorem 2.11. This is the parametrized antipodal sphere-cover specialization for the maximal real Legendrian core and its contactomorphism image. Parametrization adjustment, lift endpoint correction, smooth time flattening and ambient representative are included in this specialized formulation.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_curve_isotopy
    (F : EquivariantSphereContactomorphism) :
      ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere) ∧
        InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle) ∧
        (∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle,
          phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) ∧
        (∀ u ∈ unitCircle, k (0,u) = F.toFun ![u 0,u 1,0,0]) ∧
        (∀ u ∈ unitCircle, k (1,u) = ![u 0,u 1,0,0]) := by sorry
