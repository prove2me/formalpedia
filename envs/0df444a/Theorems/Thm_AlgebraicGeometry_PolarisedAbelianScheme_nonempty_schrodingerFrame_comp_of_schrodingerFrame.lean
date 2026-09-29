-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_schrodingerFrame_comp_of_schrodingerFrame
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.nonempty_schrodingerFrame_comp_of_schrodingerFrame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8aa572fb-95e4-5f93-ab61-cc884fdf110d
-- title:
--   Base change of a Schrödinger frame along ψ : R → R'
-- statement:
--   Fix natural numbers $g, d, n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = d$, and let $u$ be a polarised abelian scheme of type $(g,d,n)$ over a commutative ring $S$: a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on the functor of points of $f$, the property bundle, fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections whose $\mathbb{Z}/n$-combinations are bijective onto the $n$-torsion of each geometric fibre, and an invertible module $\mathcal{L} = u.\mathrm{pol}$ which is a closed immersion by sections over $f$ and has geometric fibre $H^0$-rank $d$. Let $R, R'$ be commutative rings, $t : \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism, $\zeta \in R^\times$ with $\zeta^d = 1$ and $1 - \zeta^j$ a unit for all $0 < j < d$, and $\psi : R \to R'$ a ring homomorphism. Given a Schrödinger frame $F$ for $(f, L, \mathcal{L})$ along $t$ of type $\delta$ — sections $\sigma_h$ of the pullback of $\mathcal{L}$ to $A \times_S \operatorname{Spec} R$, indexed by $H = \prod_i \mathbb{Z}/\delta_i$, such that $c \mapsto \sum_h c(h)\sigma_h$ is a bijection from $R$-valued functions on $H$ onto the global sections, together with theta points $\mathrm{lift}(h)$ acting by $\sigma_{h'} \mapsto \sigma_{h+h'}$ and theta points $\mathrm{dualLift}(\chi)$, for $\chi$ an additive character of $H$ in $R$, acting on $\sigma_h$ by the scalar $\chi(h)$ — the conclusion is that the type of Schrödinger frames for $(f, L, \mathcal{L})$ of type $\delta$ along the composite $\operatorname{Spec} R' \to \operatorname{Spec} R \to \operatorname{Spec} S$, i.e. $\operatorname{Spec}(\psi)$ followed by $t$, is nonempty.
--
--   This is the base-change stability of Schrödinger (theta) frames in Mumford's sense: a frame of type $\delta$ for the polarisation, consisting of a section basis together with compatible translation and character theta points, survives an arbitrary further base change $R \to R'$ of the parameter ring, the hypotheses on $\zeta$ supplying a strong primitive $d$-th root of unity over $R$. It is used in the construction of a cover of the base by rings over which Schrödinger frames exist, via [`AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_schrodingerFrame_comp_of_schrodingerFrame.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.nonempty_schrodingerFrame_comp_of_schrodingerFrame
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R R' : Type} [CommRing R] [CommRing R'] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j))
    (ψ : R →+* R') (F : SchrodingerFrame u.f u.L u.pol t δ) :
    Nonempty (SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t) δ) := by sorry
