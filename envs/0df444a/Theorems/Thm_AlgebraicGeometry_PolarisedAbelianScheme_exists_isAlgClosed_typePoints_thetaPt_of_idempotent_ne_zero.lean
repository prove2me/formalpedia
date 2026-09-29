-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/b9cf8ab3-f95d-5c4b-94de-0cd190615f20
-- title:
--   Typed theta points over a geometric point with pairing ζ^B
-- statement:
--   Fix naturals $g,d,n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ and $d$ non-zero and $\prod_i \delta_i = d$, a commutative ring $S$, and a polarised abelian scheme $u$ of type $(g,d,n)$ over $S$, so that $u.A \to \operatorname{Spec} S$ carries a commutative relative group law $u.L$ and an invertible, very ample module $u.\mathrm{pol}$ with geometric fibre $H^0$ of rank $d$. Let $R$ be an $S$-algebra and $\zeta \in R$ with $\zeta^d = 1$ and $1-\zeta^j$ a unit for $0<j<d$. Write $H := (\prod_i \mathbb{Z}/\delta_i) \times (\prod_i \mathbb{Z}/\delta_i)$. Assume given $x : H \to$ sections of $u.f$ over $\operatorname{Spec} R$ (morphisms $\varphi$ with $\varphi \circ u.f$ equal to the structural map) which is additive, sends $0$ to the unit section, becomes injective after base change along any ring map from $R$ to an algebraically closed field, and exhausts the kernel of the polarisation in the following local sense: for every $R$-algebra $R''$, a point $y$ over $\operatorname{Spec} R''$ satisfies `Polarisation.MemKernel` (the pullback of the Mumford bundle along the slice at $y$ is, locally on the base, isomorphic to the unit module) precisely when there are $r_1,\dots,r_m \in R''$ generating the unit ideal such that over each $\operatorname{Localization.Away} (r_j)$ the point $y$ agrees with some $x_h$. Assume further theta points $\theta^0_h$ (a point together with an isomorphism identifying the translate-pullback of $u.\mathrm{pol}$ with its pullback) with $(\theta^0_h).\mathrm{pt} = x_h$, units $e(k,k') \in R^\times$ recording the commutators of the operators $\mathrm{act}$ of the $\theta^0_k$ on global sections, a family $\varepsilon$ of complete orthogonal idempotents indexed by the $\mathbb{Z}/d$-valued pairings on $H$ with $\varepsilon_B\, e(k,k') = \varepsilon_B\, \zeta^{B(k,k')}$ for all $B,k,k'$, and a pairing $B$ with $\varepsilon_B \neq 0$. Then there exist an algebraically closed field $K$ and a ring homomorphism $\varphi : R \to K$ with $\varphi(\varepsilon_B) = 1$, together with $x^K : H \to$ sections and $\theta^K : H \to$ theta points over $\operatorname{Spec}$ of $\varphi$ composed with $S \to R$, such that each $x^K_h$ is $\operatorname{Spec}\varphi$ followed by $x_h$; $x^K_0$ is the unit section; $x^K$ is additive and injective; every point over this base in the kernel of the polarisation equals some $x^K_h$; $(\theta^K_h).\mathrm{pt} = x^K_h$; and the operators satisfy $\theta^K_k \theta^K_{k'} = \varphi(\zeta)^{B(k,k')}\,\theta^K_{k'} \theta^K_k$ on global sections, the scalar acting through `baseScalar`.
--
--   This is the specialisation step in the analysis of Mumford's theta group: the discretised commutator pairing, which over $R$ is only determined up to the idempotent decomposition, is transported to a single geometric point of the piece cut out by a non-zero idempotent $\varepsilon_B$, where it becomes literally $\varphi(\zeta)^{B}$ while the typed $K(\delta)$-level structure and its theta points survive. It is used in the proof that the commutator pairing of a rooted symmetric theta structure of the given type vanishes identically only in the degenerate case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] [NeZero d] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
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
    (hεe : ∀ (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val)
    (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (hB : ε B ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (φ : R →+* K), φ (ε B) = 1 ∧
      ∃ (xK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f)
        (θK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R))))),
        (∀ h, (xK h).1 = Spec.map (CommRingCat.ofHom φ) ≫ (x h).1) ∧
        xK 0 = u.L.one _ ∧ (∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), xK (h + h') = u.L.mul _ (xK h) (xK h')) ∧
        Function.Injective xK ∧
        (∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f, Polarisation.MemKernel u.f u.L u.pol _ y → ∃ h, y = xK h) ∧
        (∀ h, (θK h).pt = xK h) ∧
        (∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))))).obj u.pol, ⊤)),
          (θK k).act ((θK k').act s) =
            baseScalar u.f (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) (φ ζ ^ (B k k').val) • (θK k').act ((θK k).act s)) := by sorry
