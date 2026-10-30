-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_fixing_preserves_hopf
-- name    : ContactTopology.equivariant_legendrian_core_fixing_preserves_hopf
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T00:09:55.345306+00:00
-- url     : https://prove2.me/theorems/c9e018f1-826f-48ba-9d38-af9484192029
-- title:
--   Fixing a standard Legendrian core preserves the transverse Hopf class
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere commuting with the antipodal involution. Assume $F$ fixes the real Legendrian circle pointwise:
--   $$F(\cos(2\pi x),\sin(2\pi x),0,0)=(\cos(2\pi x),\sin(2\pi x),0,0)\qquad(x\in\mathbb R).$$
--   If $K\subset S^3$ is joined to the fixed positive standard Hopf circle by a smooth antipodally equivariant positive transverse isotopy, then the same is true of its image $F(K)$:
--   $$\operatorname{Nonempty}(\operatorname{EquivariantTransverseHopfIsotopy}(K))\Longrightarrow
--   \operatorname{Nonempty}(\operatorname{EquivariantTransverseHopfIsotopy}(F(K))).$$
--
--   The conclusion concerns the transverse knot class. It lets a core-alignment theorem imply regularization invariance of that class without requiring a contact isotopy of the entire sphere transformation. The input isotopy has the fixed standard Hopf starting parametrization used by the mission.
-- source:
--   Explicit standard-sphere coordinate consequence of Legendrian neighborhood fixing: Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Lemma 2.7(2), printed pp. 10–12; and transverse contact-isotopy extension: Hansjörg Geiges, Contact geometry, arXiv:math/0307242v2, https://arxiv.org/abs/math/0307242v2, Theorem 2.42 and proof, printed pp. 34–36. The explicit transverse push-off homotopy and contact commutator argument are supplied in the attached proof; standard Legendrian positive push-offs are discussed by Geiges in Section 3.6, proof of Theorem 3.20.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_fixing_preserves_hopf {K : Set Phase}
    (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ, F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
      ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0])
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (F.toFun '' K)) := by sorry
