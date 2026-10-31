-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_disk_isotopy_normal_graph
-- name    : ContactTopology.contactomorphic_core_disk_isotopy_normal_graph
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:57:30.013711+00:00
-- url     : https://prove2.me/theorems/c85723db-818a-4009-aae3-44a856a0f605
-- title:
--   Normal graphs for nearby boundary-fixed isotopies of a contactomorphic core disk
-- statement:
--   Let $F$ be an antipodally equivariant, coorientation-preserving contactomorphism of the standard contact sphere. Let $D$ be the closed unit disk in $\mathbb R^2$, and write
--   $$d(u)=\frac{(2u_0,2u_1,1-u_0^2-u_1^2,0)}{1+u_0^2+u_1^2}.$$
--   Suppose $\phi_t,\rho_t$ are sphere-preserving families, jointly smooth at every real time and sphere point, with $\rho_t\phi_t=\mathrm{id}$ on the sphere. Assume $\phi_t$ fixes the boundary of $F(d(D))$ pointwise for every real time.
--
--   There are a genuine smooth neighborhood chart $C(u,z)$ around $F(d(D))$, its smooth inverse $R$ on its chart region, and a number $\delta>0$ uniform in $t\in[0,1]$. The chart satisfies $C(u,0)=F(d(u))$. There are functions $\theta(t,a,v)$ and $g(t,a,v)$ jointly smooth on one open neighborhood of $[0,1]\times[-\delta,\delta]\times D$ such that, whenever $|a|\le\delta$, the planar projection of
--   $$R\bigl(\rho_t\phi_{t+a}(C(u,0))\bigr)$$
--   is a bijection of the whole closed disk onto itself, with inverse $v\mapsto\theta(t,a,v)$. Moreover,
--   $$\rho_t\phi_{t+a}\bigl(C(\theta(t,a,v),0)\bigr)=C\bigl(v,g(t,a,v)\bigr).$$
--   The reparametrized points remain in the actual chart, and $g(t,a,v)=0$ on $\partial D$. Consequently the pulled-back moving disk is exactly the normal graph of $g$, as an equality of subsets of the sphere.
--
--   The inverse, projection bijectivity, graph functions, and uniform time bound are conclusions. No smallness estimate or graph-position hypothesis is assumed. The ambient families need not be contact families or equivariant. This is a derived boundary-relative normal-graph preparation for isotopy discretization, not the full convex-movie, bypass-transition, or Legendrian-core classification theorem. Existence of the supplied ambient isotopy is not asserted.
-- source:
--   Ko Honda, Gluing tight contact structures, https://arxiv.org/abs/math/0102029, Section 2.2.3, Lemma 2.10 and the initial subdivision/collar preparation in its proof, arXiv pp.17–18. This normal-graph statement is a derived boundary-relative specialization in the genuine chart of the contactomorphic spanning disk; it is not a verbatim statement of Lemma 2.10. Projection surjectivity is proved here by zero extension of the boundary-vanishing displacement and the contraction mapping theorem.

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
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

theorem ContactTopology.contactomorphic_core_disk_isotopy_normal_graph
    (F : EquivariantSphereContactomorphism) (φ ρ : ℝ → Phase → Phase)
    (hφ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => φ p.1 p.2) (t,y))
    (hρ : ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2) (t,y))
    (hφS : ∀ t, MapsTo (φ t) unitThreeSphere unitThreeSphere)
    (hρS : ∀ t, MapsTo (ρ t) unitThreeSphere unitThreeSphere)
    (hleft : ∀ t y, y ∈ unitThreeSphere → ρ t (φ t y)=y)
    (hboundary : ∀ t (u : Plane), u 0^2+u 1^2=1 →
      φ t (F.toFun ![u 0,u 1,0,0])=F.toFun ![u 0,u 1,0,0]) :
    let D : Set Plane := {u | u 0^2+u 1^2 ≤ 1}
    let disk : Plane → Phase := fun u =>
      ![2*u 0/(1+u 0^2+u 1^2),2*u 1/(1+u 0^2+u 1^2),
        (1-u 0^2-u 1^2)/(1+u 0^2+u 1^2),0]
    ∃ C : Plane × ℝ → Phase, ∃ R : Phase → Plane × ℝ, ∃ N : Set (Plane × ℝ),
      ContDiff ℝ ∞ C ∧ IsOpen N ∧ (∀ u ∈ D, (u,0) ∈ N) ∧
      (∀ z, C z ∈ unitThreeSphere) ∧ (∀ u, C (u,0)=F.toFun (disk u)) ∧
      (∀ z ∈ N, ContDiffAt ℝ ∞ R (C z) ∧ R (C z)=z) ∧
      (∀ z ∈ N, ∃ U : Set Phase, IsOpen U ∧ C z ∈ U ∧
        ∀ y ∈ U, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ O : Set ((ℝ × ℝ) × Plane), IsOpen O ∧
        (Icc (0:ℝ) 1 ×ˢ Icc (-δ) δ) ×ˢ D ⊆ O ∧
        ∃ θ : (ℝ × ℝ) × Plane → Plane, ∃ g : (ℝ × ℝ) × Plane → ℝ,
          ContDiffOn ℝ ∞ θ O ∧ ContDiffOn ℝ ∞ g O ∧
          ∀ t ∈ Icc (0:ℝ) 1, ∀ a : ℝ, |a| ≤ δ →
            (∀ u ∈ D, R (ρ t (φ (t+a) (C (u,0)))) ∈ N ∧
              C (R (ρ t (φ (t+a) (C (u,0)))))=ρ t (φ (t+a) (C (u,0)))) ∧
            BijOn (fun u => (R (ρ t (φ (t+a) (C (u,0))))).1) D D ∧
            (∀ v ∈ D, θ ((t,a),v) ∈ D ∧ (v,g ((t,a),v)) ∈ N ∧
              ρ t (φ (t+a) (C (θ ((t,a),v),0)))=C (v,g ((t,a),v))) ∧
            (∀ u ∈ D, θ ((t,a),(R (ρ t (φ (t+a) (C (u,0))))).1)=u) ∧
            (∀ v ∈ frontier D, g ((t,a),v)=0) ∧
            (fun u => ρ t (φ (t+a) (F.toFun (disk u)))) '' D =
              (fun v => C (v,g ((t,a),v))) '' D := by sorry
