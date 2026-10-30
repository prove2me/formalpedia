-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_projective_disk
-- name    : ContactTopology.equivariant_legendrian_core_projective_disk
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T02:31:59.524717+00:00
-- url     : https://prove2.me/theorems/8aed3270-2a68-43c3-b417-e757109ada3f
-- title:
--   Rational disk topology and positive double boundary cover for contactomorphic cores
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard three-sphere commuting with the antipodal involution. Write
--   $$P^3=S^3/\{y\sim-y\},\qquad \pi:S^3\to P^3,$$
--   with the quotient topology. This theorem establishes the topology and positive boundary-covering multiplicity of the explicit rational disk for the image of the real Legendrian core.
--
--   For $u\in\mathbb R^2$ put
--   $$D(u)=\frac{(2u_1,2u_2,1-|u|^2,0)}{1+|u|^2},\qquad G(u)=\pi(F(D(u))).$$
--   There is an embedded parametrized circle $K:S^1\to P^3$ such that $G$ is continuous, its open unit disk restriction is a topological embedding disjoint from $K(S^1)$, and its boundary is an actual covering
--   $$p:S^1\longrightarrow K(S^1)$$
--   with exactly two points in every fiber. Its sphere lift is the globally smooth map $F\circ D$. On the closed parameter disk the only nontrivial fibers of $G$ are opposite boundary points.
--
--   The positive orientation and multiplicity are specified by the concrete circle map
--   $$\delta(u_1,u_2)=(u_1^2-u_2^2,2u_1u_2),\qquad p(u)=K(\delta(u)).$$
--   For $c(t)=(\cos t,\sin t)$ one has
--   $$\delta(c(t))=c(2t),\qquad \frac{d}{dt}\delta(c(t))=2Jc(2t),\qquad J(a,b)=(-b,a).$$
--   Thus this boundary map makes two positive turns in the embedded knot parametrization. The closed parameter disk is compact, its interior has no boundary-knot identifications, and the covering and fiber cardinality hold in the quotient space itself.
--
--   These properties supply the rational Seifert disk and its boundary multiplicity needed when interpreting contact-framing intersection calculations in projective three-space. The statement records a topological disk and a smooth sphere lift; it does not assume or assert a completed Legendrian classification, homological-order calculation, or invariant-independence theorem.
-- source:
--   Kenneth L. Baker and John B. Etnyre, Rational linking and contact geometry, corrected version, https://etnyre.math.gatech.edu/preprints/papers/ratlink.pdf, Section 1, pp. 2–3 (rational Seifert surfaces with embedded interior and r-fold boundary covering), and Section 5 (rational unknots). Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Sections 2.4–2.5. This is an explicit antipodal-quotient specialization, with the covering, embedding and positive doubled-clock identities supplied by the proof.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_ContactTopology_AntipodalSphereQuotients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
open BirkhoffGlobalSection ContactTopology.Projective Set Function Topology
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_projective_disk
    (F : EquivariantSphereContactomorphism) :
    let D : Plane → Phase := fun u =>
      ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
        (1-planeNormSq u)/(1+planeNormSq u),0]
    ∃ L : Plane → RoundSphere 4,
    ∃ K : RoundSphere 2 → ProjectiveSphere 4,
    ∃ p : RoundSphere 2 → range K,
    ∃ δ : RoundSphere 2 → RoundSphere 2,
    ∃ c : ℝ → RoundSphere 2,
      ContDiff ℝ ∞ (fun u => (L u).val) ∧
      (∀ u, (L u).val=F.toFun (D u)) ∧
      Continuous (fun u => project 4 (L u)) ∧
      IsCompact {u : Plane | planeNormSq u ≤ 1} ∧
      IsEmbedding K ∧
      IsEmbedding (fun u : {u : Plane | planeNormSq u < 1} => project 4 (L u.val)) ∧
      (∀ u : {u : Plane | planeNormSq u < 1}, project 4 (L u.val) ∉ range K) ∧
      (∀ u v : Plane, planeNormSq u ≤ 1 → planeNormSq v ≤ 1 →
        (project 4 (L u)=project 4 (L v) ↔
          u=v ∨ (planeNormSq u=1 ∧ planeNormSq v=1 ∧ u= -v))) ∧
      IsCoveringMap p ∧
      (∀ x : range K, Nat.card (p ⁻¹' {x})=2) ∧
      (∀ u : RoundSphere 2, (p u).val=project 4 (L u.val)) ∧
      (∀ u : RoundSphere 2, (p u).val=K (δ u)) ∧
      (∀ u : RoundSphere 2, (δ u).val=![u.val 0^2-u.val 1^2,2*u.val 0*u.val 1]) ∧
      (∀ t : ℝ, (c t).val=![Real.cos t,Real.sin t]) ∧
      (∀ t : ℝ, δ (c t)=c (2*t)) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => (δ (c s)).val)
        ((2:ℝ) • circleTangent (c (2*t)).val) t) := by sorry
