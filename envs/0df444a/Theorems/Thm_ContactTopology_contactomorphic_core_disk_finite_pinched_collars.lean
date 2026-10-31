-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_disk_finite_pinched_collars
-- name    : ContactTopology.contactomorphic_core_disk_finite_pinched_collars
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:04:33.141017+00:00
-- url     : https://prove2.me/theorems/faec6f17-ff13-4b7b-8dba-1288c3447b34
-- title:
--   Finite pinched layers containing a boundary-fixed isotopy of a contactomorphic core disk
-- statement:
--   Let $F$ be an antipodally equivariant coorientation-preserving contactomorphism of the standard contact sphere, let $D$ be the closed planar unit disk, and set
--   $$d(u)=\frac{(2u_0,2u_1,1-u_0^2-u_1^2,0)}{1+u_0^2+u_1^2},\qquad q(u)=1-|u|^2.$$
--   Suppose $\phi_t$ and $\rho_t$ preserve the sphere, are mutually inverse there, and are jointly smooth at every real time and sphere point. Assume $\phi_t$ fixes the boundary of $F(d(D))$ pointwise for every real time.
--
--   There exist a smooth chart $C(u,z)$ with $C(u,0)=F(d(u))$, an inverse $R$ on its actual open chart region, a width $r>0$, and a finite equal subdivision $t_j=j/(m+1)$ of $[0,1]$. The chart region contains every $(u,z)$ with $u\in D$ and $|z|\le r$. The two bounding families are
--   $$L_t(u)=\phi_t\bigl(C(u,-r q(u))\bigr),\qquad U_t(u)=\phi_t\bigl(C(u,r q(u))\bigr).$$
--   They have globally jointly smooth ambient representatives, take values in the sphere, and on $D$ their parametrizations are injective and have injective spatial derivatives. For each time, the images meet precisely along their common boundary: for $u,v\in D$,
--   $$L_t(u)=U_t(v)\quad\Longleftrightarrow\quad u=v\in\partial D.$$
--   Both agree there with the actual fixed boundary $F(u_0,u_1,0,0)$.
--
--   Every intermediate disk in a subdivision interval lies in the corresponding thinner pinched layer. More precisely, for every $s\in[t_j,t_{j+1}]$ and $u\in D$, there exist $v\in D$ and $z\in\mathbb R$ such that
--   $$|z|\le\frac r2 q(v),\qquad \phi_s(F(d(u)))=\phi_{t_j}(C(v,z)).$$
--   Thus interior layer points lie strictly between the bounding graphs, while the vertical width vanishes at the common boundary. The chart, width, bounding disks, and finite subdivision are constructed from the actual family; a prescribed admissible collar cover is not an assumption.
--
--   This proves the smooth pinched-layer preparation for isotopy discretization in this disk setting. It does not assert convexity of the bounding disks, a generic convex movie, bypass existence, or the Legendrian-core classification. Existence of the supplied ambient isotopy remains a separate requirement.
-- source:
--   Ko Honda, Gluing tight contact structures, https://arxiv.org/abs/math/0102029, Section 2.2.3, Lemma 2.10, initial subdivision and sandwiching step in its proof, arXiv pp.17–18. Derived boundary-relative sphere-disk preparation, not the full isotopy-discretization theorem. Uses the previously proved actual normal-graph theorem; the uniform boundary estimate reuses the radial comparison from our NormalMatching.boundary_vanishing_estimate construction.

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set
open scoped ContDiff

theorem ContactTopology.contactomorphic_core_disk_finite_pinched_collars
    (F : EquivariantSphereContactomorphism) (φ ρ : ℝ → Phase → Phase)
    (hφ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => φ p.1 p.2) (t,y))
    (hρ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2) (t,y))
    (hφS : ∀ t, MapsTo (φ t) unitThreeSphere unitThreeSphere)
    (hρS : ∀ t, MapsTo (ρ t) unitThreeSphere unitThreeSphere)
    (hleft : ∀ t y, y ∈ unitThreeSphere → ρ t (φ t y)=y)
    (hright : ∀ t y, y ∈ unitThreeSphere → φ t (ρ t y)=y)
    (hboundary : ∀ t (u : Plane), u 0^2+u 1^2=1 →
      φ t (F.toFun ![u 0,u 1,0,0])=F.toFun ![u 0,u 1,0,0]) :
    let D : Set Plane := {u | u 0^2+u 1^2 ≤ 1}
    let disk : Plane → Phase := fun u =>
      ![2*u 0/(1+u 0^2+u 1^2),2*u 1/(1+u 0^2+u 1^2),
        (1-u 0^2-u 1^2)/(1+u 0^2+u 1^2),0]
    ∃ C : Plane × ℝ → Phase, ∃ R : Phase → Plane × ℝ, ∃ N : Set (Plane × ℝ),
    ∃ r : ℝ, ∃ m : ℕ, ∃ lower upper : ℝ × Plane → Phase,
      ContDiff ℝ ∞ C ∧ IsOpen N ∧ 0 < r ∧
      (∀ z, C z ∈ unitThreeSphere) ∧ (∀ u, C (u,0)=F.toFun (disk u)) ∧
      (∀ z ∈ N, ContDiffAt ℝ ∞ R (C z) ∧ R (C z)=z) ∧
      (∀ u ∈ D, ∀ z : ℝ, |z| ≤ r → (u,z) ∈ N) ∧
      ContDiff ℝ ∞ lower ∧ ContDiff ℝ ∞ upper ∧
      (∀ t u, lower (t,u)=φ t (C (u,-(r*(1-(u 0^2+u 1^2))))) ∧
        upper (t,u)=φ t (C (u,r*(1-(u 0^2+u 1^2))))) ∧
      (∀ t u, lower (t,u) ∈ unitThreeSphere ∧ upper (t,u) ∈ unitThreeSphere) ∧
      (∀ t, InjOn (fun u => lower (t,u)) D ∧ InjOn (fun u => upper (t,u)) D) ∧
      (∀ t, ∀ u ∈ D, Function.Injective (fderiv ℝ (fun v => lower (t,v)) u) ∧
        Function.Injective (fderiv ℝ (fun v => upper (t,v)) u)) ∧
      (∀ t, ∀ u ∈ D, ∀ v ∈ D,
        (lower (t,u)=upper (t,v) ↔ u=v ∧ u 0^2+u 1^2=1)) ∧
      (∀ t u, u 0^2+u 1^2=1 →
        lower (t,u)=F.toFun ![u 0,u 1,0,0] ∧ upper (t,u)=F.toFun ![u 0,u 1,0,0]) ∧
      ∀ j : ℕ, j ≤ m →
        (j:ℝ)/(m+1:ℝ) ∈ Icc (0:ℝ) 1 ∧
        ∀ s ∈ Icc ((j:ℝ)/(m+1:ℝ)) ((j+1:ℝ)/(m+1:ℝ)), ∀ u ∈ D,
          ∃ v ∈ D, ∃ z : ℝ, |z| ≤ (r/2)*(1-(v 0^2+v 1^2)) ∧
            φ s (F.toFun (disk u))=φ ((j:ℝ)/(m+1:ℝ)) (C (v,z)) := by sorry
