-- Prove2me | Theorems.Thm_ContactTopology_explicit_two_arc_convex_disk_in_standard_contact_space
-- name    : ContactTopology.explicit_two_arc_convex_disk_in_standard_contact_space
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T05:33:03.463994+00:00
-- url     : https://prove2.me/theorems/d743df71-f96b-4e05-8905-a1a056eddeb9
-- title:
--   An explicit convex disk with Legendrian boundary and two dividing arcs in standard contact space
-- statement:
--   In standard contact three-space with coordinates $(Q,P,Z)$ and contact form $\alpha=dZ-P\,dQ$, there is an explicit smooth embedded disk with Legendrian boundary, an actual smooth transverse contact vector field, and exactly two dividing arcs.
--
--   For $x=(u,v)$ write $R=u^2+v^2$ and define
--   $$f(u,v)=u^2-v^2-\frac{1+R^2}{4},\qquad
--   \beta=(f_v-2fv)\,du+(-f_u+2fu)\,dv.$$
--   Let $Z(u,v)$ be the polynomial primitive $\int_0^v\beta_1(u,s)\,ds$ and put $P(u,v)=\partial_u Z(u,v)-\beta_0(u,v)$. The explicit disk is
--   $$j(u,v)=(u,P(u,v),Z(u,v)),\qquad u^2+v^2\le1.$$
--   Its ambient formula is globally smooth, it embeds the closed unit disk, and its derivative is injective at every point of that disk, including its boundary. It satisfies $j^*\alpha=\beta$, and the boundary circle is Legendrian.
--
--   The theorem constructs a globally smooth compactly supported Hamiltonian $H:\mathbb R^3\to\mathbb R$. Its actual contact field is
--   $$X_H=(-H_P,\ H_Q+P H_Z,\ H-PH_P).$$
--   This field is globally smooth and satisfies the contact Lie identity $\mathcal L_{X_H}\alpha=H_Z\alpha$. On the disk it is transverse to every tangent plane and
--   $$\alpha_{j(u,v)}(X_H(j(u,v)))=f(u,v).$$
--
--   Define
--   $$A(t)=2-t^2-\sqrt{3-8t^2},\qquad
--   \gamma_\pm(t)=j(\pm\sqrt{A(t)},t),\qquad -\tfrac12\le t\le\tfrac12.$$
--   Both radicands are positive on a neighborhood of this interval. Each $\gamma_\pm$ is a smooth regular embedded arc; their images are disjoint. Each meets the physical disk boundary only at its two endpoints. The entire physical dividing locus is exactly
--   $$\{j(u,v):u^2+v^2\le1,\ \alpha(X_H)=0\}
--   =\operatorname{im}(\gamma_+)\cup\operatorname{im}(\gamma_-).$$
--   The field, its transversality and the complete dividing-set description are conclusions, not hypotheses or certificates. This is a construction in standard contact three-space. The required placement near the mission's actual torus and comparison knots, sphere/projective contact-field transfer, boundary-parallel cap data, bypass attachment and core classification are further steps.
-- source:
--   Explicit derived local construction toward the bypass preparation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Theorem 2.2 and Proposition 3.3. These sources motivate the need for a convex Legendrian-boundary disk with multiple dividing arcs; the polynomial invariant form, its explicit embedded realization in standard contact three-space, the compact Hamiltonian extension and the complete two-arc description are auxiliary constructions supplied here, not statements quoted from Min. No bypass attachment, tightness classification, placement relative to the mission comparison knots, or Legendrian core classification is asserted.

import Definitions.Def_ContactTopology_TwoArcJetDisk
import Mathlib.Topology.Algebra.Support
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function Topology
open scoped ContDiff

theorem ContactTopology.explicit_two_arc_convex_disk_in_standard_contact_space :
    ContDiff ℝ ∞ jetDisk ∧
    IsEmbedding (fun x : {x : Plane // radiusSq x≤1} => jetDisk x.val) ∧
    (∀ x : Plane, radiusSq x≤1 → Injective (fderiv ℝ jetDisk x)) ∧
    (∀ x ∈ unitCircle, jetForm (jetDisk x) (fderiv ℝ jetDisk x (circleTangent x))=0) ∧
    (∀ σ : ℝ, σ^2=1 → IsEmbedding (jetDividingArc σ) ∧
      (∀ t ∈ Icc (-1/2:ℝ) (1/2), ContDiffAt ℝ ∞ (jetDisk ∘ arc σ) t ∧
        deriv (jetDisk ∘ arc σ) t≠0) ∧
      (∀ t : Icc (-1/2:ℝ) (1/2), jetDividingArc σ t ∈ jetDisk '' unitCircle ↔
        t.val= -1/2 ∨ t.val=1/2)) ∧
    Disjoint (range (jetDividingArc 1)) (range (jetDividingArc (-1))) ∧
    ∃ H : Space → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ContDiff ℝ ∞ (jetContactField H) ∧
      (∀ y v, -(jetContactField H y 1)*v 0+jetForm y (fderiv ℝ (jetContactField H) y v)=
        fderiv ℝ H y (Pi.single 2 1)*jetForm y v) ∧
      (∀ x : Plane, radiusSq x≤1 →
        (∀ w : Plane, jetContactField H (jetDisk x)≠fderiv ℝ jetDisk x w) ∧
        jetForm (jetDisk x) (jetContactField H (jetDisk x))=dividing x) ∧
      {y : Space | ∃ x : Plane, radiusSq x≤1 ∧ jetDisk x=y ∧ jetForm y (jetContactField H y)=0}=
        range (jetDividingArc 1) ∪ range (jetDividingArc (-1)) := by sorry
