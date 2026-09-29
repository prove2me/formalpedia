-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/324166a3-9950-51f5-9367-0c905f1a4369
-- title:
--   Normal form of a theta point on a Schrödinger frame
-- statement:
--   Fix natural numbers $g, N, n$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = N+1$; write $H = \prod_i \mathbb{Z}/\delta_i$. Let $S$ be a commutative ring in which $N+1$ is invertible, let $\zeta \in S$ satisfy $\zeta^{N+1} = 1$ with $1-\zeta^j$ a unit for all $0 < j < N+1$, and let $\omega \in S$ satisfy $\omega^2 = \zeta$. Let $X$ be a framed polarised abelian scheme of type $(g, N, n)$ over $S$: a commutative relative group law $X.L$ on $X.f : A \to \operatorname{Spec} S$ with the abelian-scheme property bundle, fibres of dimension $g$, the $2g$ marked $n$-torsion sections generating the geometric $n$-torsion freely, an invertible module $X.pol$ that is very ample by sections with geometric fibre $H^0$-rank $N+1$, together with a projective presentation of $X.pol$ by $N+1$ global sections giving a closed immersion into $\mathbb{P}^N_S$ whose section system is a basis. Let $F$ be a Schrödinger frame of type $\delta$ for $X.pol$ over the identity of $\operatorname{Spec} S$, that is sections $F.\sigma_x$ ($x \in H$) of the pullback of $X.pol$ forming a basis of global sections, together with translation theta points $F.\mathrm{lift}$ and character theta points $F.\mathrm{dualLift}$ acting on the $F.\sigma_x$ by $F.\sigma_{h+x}$ and by scalars $\chi(x)$ respectively. Let $\theta$ be an arbitrary theta point for $X.pol$ over the identity, namely a section of $X.f$ together with an isomorphism identifying the translate of the pulled-back module with itself. Then there exist a function $\varepsilon : H \times H \to S$ and a unit $u \in S^\times$ such that the $\varepsilon(c)$ form a complete family of orthogonal idempotents, and for every $c = (c_1,c_2) \in H \times H$ and every $x \in H$,
--   $$\varepsilon(c)\cdot \theta.\mathrm{act}(F.\sigma_x) = \bigl(\varepsilon(c)\, u\, \omega^{\langle c_2, x\rangle}\bigr)\cdot F.\sigma_{x + c_1},$$
--   where scalars from $S$ act through `baseScalar` and $\omega^{\langle c_2, x\rangle}$ denotes `ThetaLevel.thetaChar` $\delta\,(N+1)\,S\,\omega$ evaluated at $(c_2, x)$, i.e. $\omega$ raised to the representative in $\mathbb{Z}/2(N+1)$ of the pairing $\sum_i \iota_i(c_{2,i}x_i)$.
--
--   This is the structure theorem for the theta group of Mumford, in the form that says that after decomposing $\operatorname{Spec} S$ into the clopen pieces cut out by a complete family of orthogonal idempotents, any theta point acts on a Schrödinger frame as a unit scalar times a standard translation operator composed with a standard character operator; over connected $S$ a single index pair $(c_1,c_2)$ serves. It is used to pin down the action of theta points on framed sections, feeding the description of the theta level structures attached to a framed polarised abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (S : Type) [CommRing S] (hd : IsUnit ((N + 1 : ℕ) : S))
    (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : S) (hω : ω ^ 2 = ζ)
    (X : FramedPolarisedAbelianScheme g N n S)
    (F : SchrodingerFrame X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) δ)
    (θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S)))) :
    ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
      ∀ (c : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) (x : ((i : Fin g) → ZMod (δ i))),
        baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (ε c) • θ.act (F.σ x) =
          baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (ε c * u * ThetaLevel.thetaChar δ (N + 1) S ω c.2 x) •
            F.σ (x + c.1) := by sorry
