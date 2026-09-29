-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_forall_eq_zero_of_commutatorPairing_of_rootedSymmetricOfType
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.forall_eq_zero_of_commutatorPairing_of_rootedSymmetricOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/abb080d0-0959-5def-a906-c68921f4cdff
-- title:
--   Non-degeneracy of the commutator pairing on each idempotent piece
-- statement:
--   Fix naturals $g,d,n$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ and $d$ nonzero and $\prod_i \delta_i = d$, a commutative ring $S$ in which $d$ is a unit, and $u$ a term of `PolarisedAbelianScheme g d n S` (a scheme $A$ with structure morphism $u.f$ to $\operatorname{Spec} S$, a commutative relative group law $u.L$, an abelian-scheme property bundle, fibres of topological Krull dimension $g$, $2g$ sections killed by $n$ that are independent and generate the $n$-torsion of every geometrically closed fibre, and an invertible module $u.pol$ which is very ample via sections and has geometric fibre $H^0$-rank $d$), assumed to satisfy `Polarisation.IsSymmetric`, `IsOfType δ` and `HasPrincipalRoot`. Let $R$ be an $S$-algebra and $\zeta \in R$ with $\zeta^d = 1$ and $1 - \zeta^j$ a unit for $0 < j < d$. Write $K(\delta) = \big(\prod_i \mathbb{Z}/\delta_i\big)^2$. Let $x : K(\delta) \to$ sections of $u.f$ over $\operatorname{Spec} R$ send $0$ to the identity section and sums to products under $u.L$, be injective after base change along every ring homomorphism from $R$ to an algebraically closed field, and exhaust the polarisation kernel in the sense that for every $R$-algebra $R''$ a section $y$ over $\operatorname{Spec} R''$ satisfies `Polarisation.MemKernel` for $u.f, u.L, u.pol$ precisely when there are $r_1,\dots,r_m \in R''$ generating the unit ideal such that over each $\operatorname{Localization.Away}(r_j)$ the section $y$ coincides with the base change of some $x\,h$. Let $\theta_0 : K(\delta) \to \mathrm{ThetaPt}$ lift $x$ (each $(\theta_0 k).pt = x\,k$), let $e : K(\delta) \times K(\delta) \to R^{\times}$ record the commutators of the induced operators on global sections of the pullback of $u.pol$, i.e. $(\theta_0 k).act \circ (\theta_0 k').act = e(k,k') \cdot (\theta_0 k').act \circ (\theta_0 k).act$, and let $\varepsilon$ be a family of complete orthogonal idempotents of $R$ indexed by the $\mathbb{Z}/d$-valued functions $B$ on $K(\delta) \times K(\delta)$, with $\varepsilon_B\, e(k,k') = \varepsilon_B\, \zeta^{(B(k,k')).val}$ for all $B,k,k'$. The conclusion: for every $B$ with $\varepsilon_B \neq 0$ and every $k \in K(\delta)$, if $B(k,k') = 0$ for all $k'$ then $k = 0$.
--
--   This is the non-degeneracy of the Weil commutator pairing on the kernel of a polarisation, in the piecewise form adapted to a base ring that is decomposed by the idempotents $\varepsilon_B$: on each piece where $\varepsilon_B$ does not vanish, the $\mathbb{Z}/d$-valued pairing $B$ computing the commutators has trivial left radical. It feeds the construction of level lifts for symmetric, principally rooted polarisations of type $\delta$ (`exists_levelLifts_of_rootedSymmetricOfType`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_forall_eq_zero_of_commutatorPairing_of_rootedSymmetricOfType.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.forall_eq_zero_of_commutatorPairing_of_rootedSymmetricOfType
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] [NeZero d] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S) (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u)
    {R : Type} [CommRing R] [Algebra S R]
    (ζ : R) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S R))) u.f)
    (hx0 : x 0 = u.L.one _) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul _ (x h) (x h'))
    (hxinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) (h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))),
      Spec.map (CommRingCat.ofHom sk) ≫ (x h).1 = Spec.map (CommRingCat.ofHom sk) ≫ (x h').1 → h = h')
    (hxK : ∀ (R'' : Type) [CommRing R''] [Algebra R R'']
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap R R'').comp (algebraMap S R)))) u.f),
      Polarisation.MemKernel u.f u.L u.pol _ y ↔
        ∃ (m : ℕ) (r : Fin m → R''), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))),
          Spec.map (CommRingCat.ofHom (algebraMap R'' (Localization.Away (r j)))) ≫ y.1 =
            Spec.map (CommRingCat.ofHom ((algebraMap R'' (Localization.Away (r j))).comp (algebraMap R R''))) ≫ (x h).1)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S R)))) (hθ₀ : ∀ k, (θ₀ k).pt = x k)
    (e : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → Rˣ)
    (he : ∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))).obj u.pol, ⊤)),
      (θ₀ k).act ((θ₀ k').act s) = baseScalar u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) (e k k' : R) • (θ₀ k').act ((θ₀ k).act s))
    (ε : ((((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) → R) (hε : CompleteOrthogonalIdempotents ε)
    (hεe : ∀ (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val) :
    ∀ B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d, ε B ≠ 0 →
      ∀ k : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), (∀ k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), B k k' = 0) → k = 0 := by sorry
