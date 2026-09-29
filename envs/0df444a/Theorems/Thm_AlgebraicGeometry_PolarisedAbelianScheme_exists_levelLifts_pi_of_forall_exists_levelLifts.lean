-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_pi_of_forall_exists_levelLifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8cc94f2e-bed4-569f-8891-84cbed22df30
-- title:
--   Level lifts over a finite product of test rings
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ of nonzero entries, and write $H(\delta) = \prod_{i} \mathbb{Z}/\delta(i)$. Let $S$ be a commutative ring and let $u$ be a polarised abelian scheme of the project's kind over $S$: a morphism $u.f : A \to \operatorname{Spec} S$ with a commutative relative group law $u.L$, the abelian-scheme property bundle, all fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections independent and spanning on geometric fibres, and an invertible module $u.pol$ which is a closed immersion by sections with geometric fibre $H^0$-rank $d$. Let $m$ be a natural number, let $R_p$ ($p \in \mathrm{Fin}\,m$) be commutative rings with ring homomorphisms $\varphi_p : S \to R_p$ and units $\zeta_p \in R_p^{\times}$. The hypothesis is that for each $p$ there are maps $\mathrm{lift} : H(\delta) \to \mathrm{ThetaPt}\,u.f\,u.L\,u.pol$ over $\operatorname{Spec} R_p \to \operatorname{Spec} S$ and $\mathrm{dualLift} : \operatorname{Hom}(H(\delta), \mathbb{Z}/d) \to \mathrm{ThetaPt}\,u.f\,u.L\,u.pol$ over the same base change, each sending $0$ to $1$ and sums to products, and satisfying the commutation rule $\mathrm{dualLift}(c)\cdot \mathrm{lift}(h) = \mathrm{ofScalar}(\zeta_p^{\,(c\,h).\mathrm{val}})\cdot(\mathrm{lift}(h)\cdot \mathrm{dualLift}(c))$, where a theta point consists of a point of $A$ over the base together with an isomorphism between the pullback of $u.pol$ along the translation by that point and the pullback of $u.pol$, and $\mathrm{ofScalar}$ is the theta point attached to a unit of the base ring. The conclusion asserts the existence of such a pair $(\mathrm{lift}, \mathrm{dualLift})$ with the same three properties over the product ring $\prod_p R_p$, for the base change along `RingHom.pi φ` and with the unit $\zeta = (\zeta_p)_p$ of $\prod_p R_p$ obtained from the tuple of units via `MulEquiv.piUnits`.
--
--   This is the product, or gluing, step in the construction of level lifts (in Mumford's language, homomorphic lifts of the two halves of a symplectic decomposition of $H(\delta) \oplus \widehat{H(\delta)}$ into the theta group of the polarisation, with the Heisenberg commutator rule for a chosen unit): since $\operatorname{Spec}$ of a finite product of rings is the disjoint union of the spectra of the factors, level lifts over each factor assemble into a level lift over the product. It feeds the construction of level lifts for rooted symmetric data, [`AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_rootedSymmetricOfType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_rootedSymmetricOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_pi_of_forall_exists_levelLifts
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {m : ℕ} (Rp : Fin m → Type) [∀ p, CommRing (Rp p)] (φ : ∀ p, S →+* Rp p) (ζ : ∀ p, (Rp p)ˣ)
    (hL : ∀ p : Fin m,
      ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ p))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ p)))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h = ThetaPt.ofScalar (ζ p ^ (c h).val) * (lift h * dualLift c))) :
    ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (RingHom.pi φ))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (RingHom.pi φ)))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h = ThetaPt.ofScalar (MulEquiv.piUnits.symm ζ ^ (c h).val) * (lift h * dualLift c)) := by sorry
