-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7b90e4e2-65a0-5a0a-8a99-3c07a4241211
-- title:
--   Central theta points lie over the identity section
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and a vector $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero and $\prod_i \delta_i = d$. Let $S$ be a commutative ring in which the image of $d$ is a unit, and let $u$ be a polarised abelian scheme of invariants $(g,d,n)$ over $S$: an $S$-scheme $u.f : A \to \operatorname{Spec} S$ with a commutative relative group law $u.L$, an abelian-scheme property bundle, fibres of topological Krull dimension $g$, $2g$ marked $n$-torsion sections generating the geometric $n$-torsion freely, and an invertible module $u.pol$ that is a closed immersion by sections with geometric fibre $H^0$-rank $d$. Assume $u$ is rooted symmetric of type $\delta$, that is: $u.pol$ pulled back along the inversion morphism is locally isomorphic over the base to $u.pol$, $u$ is of type $\delta$, and $u$ has a principal root. Let $K$ be an algebraically closed field and $t : \operatorname{Spec} K \to \operatorname{Spec} S$. Let $x$ be a map from $H = (\prod_i \mathbb{Z}/\delta_i) \times (\prod_i \mathbb{Z}/\delta_i)$ to the sections of $u.f$ over $t$ (morphisms $\varphi$ with $\varphi$ followed by $u.f$ equal to $t$) which sends $0$ to the identity section, is additive for the group law $u.L$, is injective, and is surjective onto those sections $y$ satisfying `Polarisation.MemKernel u.f u.L u.pol t y`, i.e. the pullback of the Mumford bundle of $u.pol$ along the slice at $y$ is locally isomorphic over the base to the unit module. Let $\theta_0 : H \to$ `ThetaPt u.f u.L u.pol t` be a family of theta points — pairs consisting of a section and an isomorphism between the pullback of $u.pol|_{A\times_S K}$ along translation by that section and $u.pol|_{A \times_S K}$ — with $(\theta_0 h).pt = x\,h$ for all $h$, and let $\theta$ be a further theta point whose induced action on the global sections of the pullback of $u.pol$ along the first projection $A\times_S \operatorname{Spec} K \to A$ commutes with the action of every $\theta_0 h$. Then $\theta.pt$ is the identity section $u.L.one\,t$.
--
--   This is the statement that the centre of the theta group of a symmetric, principally rooted polarisation of type $\delta$ over an algebraically closed field consists of theta points lying over the identity: commuting with a full set of theta points above the kernel $K(\mathcal L)$ forces the underlying point to be trivial. It is the nondegeneracy input used by [`AlgebraicGeometry.PolarisedAbelianScheme.forall_eq_zero_of_commutatorPairing_of_rootedSymmetricOfType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.forall_eq_zero_of_commutatorPairing_of_rootedSymmetricOfType), which extracts from it the nondegeneracy of the commutator pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S) (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hx0 : x 0 = u.L.one t) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul t (x h) (x h'))
    (hxinj : Function.Injective x)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y → ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ h, (θ₀ h).pt = x h)
    (θ : ThetaPt u.f u.L u.pol t)
    (hcomm : ∀ (h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
      θ.act ((θ₀ h).act s) = (θ₀ h).act (θ.act s)) :
    θ.pt = u.L.one t := by sorry
