-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/ed369887-eae0-5dcc-901a-bdbdf2796d11
-- title:
--   Schrödinger frames on a basic-open cover from level lifts
-- statement:
--   Fix natural numbers $g,d,n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = d$, and write $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $S$ be a commutative ring and $u$ a `PolarisedAbelianScheme g d n S`, that is: a scheme $A$ with a morphism $f = u.f : A \to \operatorname{Spec} S$, a commutative relative group law $L = u.L$ on $f$, the property bundle `AbelianSchemePropertyBundle`, all fibres of topological Krull dimension $g$, sections $P_1,\dots,P_{2g}$ of $f$ killed by $n$ which on every geometric fibre are independent of order $n$ and span the $n$-torsion, together with a module $\mathcal{L} = u.\mathrm{pol}$ on $A$ which is invertible, admits a projective presentation whose associated morphism is a closed immersion, and has geometric fibre $H^0$-rank $d$. Let $R$ be a commutative ring and $t : \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism, assume $d$ is a unit in $R$, and let $\zeta \in R^\times$ satisfy $\zeta^d = 1$ and $1 - \zeta^j \in R^\times$ for all $0 < j < d$. Assume given $d$ global sections $\sigma^0_1,\dots,\sigma^0_d$ of the pullback of $\mathcal{L}$ along $\mathrm{pullback.fst}\,u.f\,t$ which form a basis in the sense of `Scheme.Modules.IsSectionBasis` for $\mathrm{pullback.snd}\,u.f\,t$, i.e. the map sending $c \in R^d$ to $\sum_i c_i \cdot \sigma^0_i$ (scalars transported through the structure morphism) is bijective. Assume further two maps into the theta points `ThetaPt u.f u.L u.pol t` (pairs consisting of a point of $A$ over $t$ and an isomorphism between the translate-pullback of the pulled-back $\mathcal{L}$ and the pulled-back $\mathcal{L}$): a map $\mathrm{lift}$ on $H(\delta)$ and a map $\mathrm{dualLift}$ on $\mathrm{Hom}(H(\delta), \mathbb{Z}/d)$, each sending $0$ to $1$ and sums to products, subject to the Heisenberg commutation rule $\mathrm{dualLift}(c)\,\mathrm{lift}(h) = \mathrm{ofScalar}(\zeta^{\widetilde{c(h)}})\,\bigl(\mathrm{lift}(h)\,\mathrm{dualLift}(c)\bigr)$, where $\widetilde{c(h)}$ denotes the canonical representative of $c(h) \in \mathbb{Z}/d$. The conclusion is that there exist $m \in \mathbb{N}$ and $r_1,\dots,r_m \in R$ generating the unit ideal such that for each $j$ the type `SchrodingerFrame u.f u.L u.pol` of type $\delta$ is nonempty over the base $\operatorname{Spec}$ of the localisation $R[1/r_j]$ mapping to $\operatorname{Spec} R$ and then by $t$ to $\operatorname{Spec} S$: that is, there are sections $\sigma_h$ indexed by $h \in H(\delta)$ forming an $R[1/r_j]$-basis of the global sections of the pulled-back $\mathcal{L}$, together with theta points $\mathrm{lift}(h)$ acting by $\sigma_{h'} \mapsto \sigma_{h+h'}$ and theta points $\mathrm{dualLift}(\chi)$, for additive characters $\chi$ of $H(\delta)$ with values in $R[1/r_j]$, acting on $\sigma_h$ by the scalar $\chi(h)$.
--
--   This is the Stone–von Neumann–Mackey step in the construction of theta structures, in the form needed over a base ring: a pair of commuting level lifts satisfying the Heisenberg rule can be normalised, after passing to a cover of $\operatorname{Spec} R$ by basic opens, to a Schrödinger basis of sections on which the lifts act by translation and by characters. It feeds the companion statement [`AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (hdR : IsUnit ((d : ℕ) : R))
    (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j))
    (σ₀ : Fin d → Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤))
    (hσ₀ : Scheme.Modules.IsSectionBasis (pullback.snd u.f t) ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) σ₀)
    (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol t)
    (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol t)
    (hl0 : lift 0 = 1) (hlmul : ∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h')
    (hd0 : dualLift 0 = 1) (hdmul : ∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c')
    (hHeis : ∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
      dualLift c * lift h = ThetaPt.ofScalar (ζ ^ (c h).val) * (lift h * dualLift c)) :
    ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : Fin m, Nonempty (SchrodingerFrame u.f u.L u.pol
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ t) δ) := by sorry
