-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4b153be6-a897-5e5a-b99e-4c5dfdda3efa
-- title:
--   Theta points at the identity act by a unit scalar
-- statement:
--   Fix natural numbers $g,d,n$ and a commutative ring $S$, and let $u$ be a polarised abelian scheme of type $(g,d,n)$ over $S$: a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on the functor of points of $f$ (functorial multiplication, unit and inverse on $S$-morphisms into $A$, with the group axioms and compatibility under base change) that is commutative, an `AbelianSchemePropertyBundle` for $f$, fibres of topological Krull dimension $g$, a family $P_i$ ($i \in \mathrm{Fin}(2g)$) of $n$-torsion sections which on every geometric fibre freely generate the $n$-torsion, and a module `pol` on $A$ that is invertible (locally isomorphic to the structure sheaf), defines a closed immersion into a projective space by its sections relative to $f$, and has geometric fibre $H^0$-rank $d$. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and let $\theta$ be a theta point of `pol` over $t$, that is, a section $\theta.\mathrm{pt}$ of $f$ over $t$ together with an isomorphism $\theta.\mathrm{iso}$ between the translate by $\theta.\mathrm{pt}$ of the pullback of `pol` to $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ and that pullback itself. Assume $\theta.\mathrm{pt}$ is the unit section $L.\mathrm{one}\, t$. Then there is a unit $c \in R^\times$ such that for every global section $s$ of the pulled-back module on $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$, the action $\theta.\mathrm{act}\, s$ — the image under $\theta.\mathrm{iso}$ of the canonical pullback of $s$ along the translation — equals $\mathrm{baseScalar}\, c \cdot s$, where $\mathrm{baseScalar}\, c$ is the image of $c$ in $\Gamma(A \times_{\operatorname{Spec} S} \operatorname{Spec} R, \mathcal{O})$ under the structural map.
--
--   This is the statement that the kernel of the map from the theta group to the points of the abelian scheme consists of scalars, i.e. that the centre of Mumford's theta group $\mathcal{G}(\mathcal{L})$ is $\mathbb{G}_m$, here in the relative form over an arbitrary test ring $R$. It is used in the construction of the commutator pairing on theta points, in the extraction of a symmetric cocycle measuring the failure of commutativity of the theta action, and in comparing iterated theta actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (θ : ThetaPt u.f u.L u.pol t) (hθ : θ.pt = u.L.one t) :
    ∃ c : Rˣ, ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤),
      θ.act s = baseScalar u.f t (c : R) • s := by sorry
