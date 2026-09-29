-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_schrodingerFrame_of_levelLifts
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7d6d9d34-e429-59b9-8b13-34bf8781b384
-- title:
--   Heisenberg level lifts give Schrödinger frames Zariski-locally
-- statement:
--   Fix natural numbers $g,d,n$ and a type $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = d$, and let $u$ be a polarised abelian scheme of type $(g,d,n)$ over a commutative ring $S$: a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on the functor $t \mapsto \{\varphi \mid \varphi \circ f = t\}$, the abelian-scheme property bundle for $f$, fibres of topological Krull dimension $g$, $2g$ sections $P_i$ that are $n$-torsion and form a basis of the $n$-torsion of every geometric fibre, and an invertible module `pol` on $A$ which is a closed immersion by sections over $S$ and has geometric fibre $H^0$-rank $d$. Let $S_1$ be an $S$-algebra in which $d$ is a unit, and $\zeta \in S_1^\times$ with $\zeta^d = 1$ and $1 - \zeta^j$ a unit for all $0 < j < d$. Let `lift` be a map from $H(\delta) = \prod_i \mathbb{Z}/\delta_i$ and `dualLift` a map from $\mathrm{Hom}(H(\delta), \mathbb{Z}/d)$ into the theta points of `pol` over $S_1$ (pairs consisting of a point of $A$ over $\operatorname{Spec} S_1$ together with an isomorphism between the translate of the pulled-back `pol` by that point and the pulled-back `pol` itself), both sending $0$ to $1$ and sums to products, and satisfying the Heisenberg rule $\mathrm{dualLift}(c)\,\mathrm{lift}(h) = [\zeta^{c(h)}]\,(\mathrm{lift}(h)\,\mathrm{dualLift}(c))$, where $[\,\cdot\,]$ is the central theta point attached to a unit of the base ring. The conclusion: there are $m \in \mathbb{N}$ and $r : \mathrm{Fin}\,m \to S_1$ whose range generates the unit ideal of $S_1$, such that for each $j$ a Schrödinger frame of type $\delta$ for `pol` exists over $S_1[1/r_j]$ (regarded as an $S$-algebra through $S \to S_1 \to S_1[1/r_j]$): that is, sections $\sigma_h$ of the pulled-back `pol` indexed by $h \in H(\delta)$ such that $c \mapsto \sum_h c(h)\sigma_h$ is bijective, together with level lifts and dual lifts (the latter indexed by additive characters of $H(\delta)$ with values in the base ring) acting on the $\sigma_h$ by $\sigma_{h'} \mapsto \sigma_{h+h'}$ and by the scalar $\chi(h)$ respectively.
--
--   This is the Stone–von Neumann–Mackey statement for the theta group of a polarised abelian scheme in the relative, ring-theoretic setting: an abstract Heisenberg-type pair of commuting level lifts is rigidified into an explicit Schrödinger model of the space of sections, after passing to a Zariski cover of the base on which the sections form a free basis. It is used in the construction of Schrödinger frames for symmetric line bundles with a chosen root, via [`AlgebraicGeometry.PolarisedAbelianScheme.exists_schrodingerFrame_of_rootedSymmetricOfType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_schrodingerFrame_of_rootedSymmetricOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_schrodingerFrame_of_levelLifts.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (S₁ : Type) [CommRing S₁] [Algebra S S₁] (hd₁ : IsUnit ((d : ℕ) : S₁))
    (ζ : S₁ˣ) (hζ : (ζ : S₁) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : S₁) ^ j))
    (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
    (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
    (hl0 : lift 0 = 1) (hlmul : ∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h')
    (hd0 : dualLift 0 = 1) (hdmul : ∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c')
    (hHeis : ∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
      dualLift c * lift h = ThetaPt.ofScalar (ζ ^ (c h).val) * (lift h * dualLift c)) :
    ∃ (m : ℕ) (r : Fin m → S₁), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : Fin m, Nonempty (SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom ((algebraMap S₁ (Localization.Away (r j))).comp (algebraMap S S₁)))) δ) := by sorry
