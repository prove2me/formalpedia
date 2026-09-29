-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_opens_isClosed_range_subset_iff_trace
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/2629b63a-66c0-5362-bf76-c2be2dd36754
-- title:
--   Drinfeld's trace condition cuts out a clopen locus
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order maximal under inclusion among orders), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar x\,\mu$, and let $\beta:\mathrm{Fin}\,4\to\Lambda$ be a $\mathbb{Z}$-basis of $\Lambda$ (every element of $\Lambda$ is uniquely an integral combination of the $\beta_j$). Let $d,m$ be naturals with $m\ge 3$, let $R$ be a commutative ring in which $m$ is a unit, and let $X$ be a polarised abelian scheme of relative dimension $2$, geometric fibre degree $d$ and full level $m$ over $\mathrm{Spec}\,R$, with relative group law $X.L$ on $X.f:X.A\to\mathrm{Spec}\,R$. Let $\pi_E:E\to\mathrm{Spec}\,R$ be a scheme over $\mathrm{Spec}\,R$ together with a family $\mathrm{cl}$ assigning, to each ring map $\varphi:R\to R'$, each relative group law $L'$ on $f':A'\to\mathrm{Spec}\,R'$ exhibited by $g:A'\to X.A$ as a pullback of $X.L$ along $\varphi$ (`IsGroupPullback`), and each action of $\Lambda$ on $(f',L')$ by endomorphisms over the base which are additive in both senses and multiplicative (`LatticeAction`), a section of $\pi_E$ over $\mathrm{Spec}\,\varphi$; assume `RepresentsLatticeActions`, i.e. $\mathrm{cl}$ is compatible with further base change and is, for each such $(\varphi,L',g)$, a bijection from $\Lambda$-actions to sections. Then there is an open $U\subseteq E$ whose underlying set is closed, such that for all $\varphi,L',g$ as above and every $\Lambda$-action $i'$ on $(f',L')$, the topological image of the section $\mathrm{cl}(\varphi,L',g,i')$ lies in $U$ if and only if the following trace condition holds: for every algebraically closed field $k$, every ring map $s_k:R'\to k$, every finite-dimensional $k$-space $V$ and every injection $\tau:V\to\mathrm{Hom}_{\mathrm{tangentBase}\,k\,s_k}(f')$ whose range is exactly the tangent vectors of $L'$ at the geometric point, which is additive for $L'.\mathrm{mul}$ and compatible with scalars via `tangentScale`, and for every $x\in\Lambda$, every $k$-linear $\Phi:V\to V$ with $\tau(\Phi v)=i'.\mathrm{act}(x)_*\tau(v)$ for all $v$, and every integer $n$ with $x+\bar x=n$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\mathrm{tr}_k(\Phi)=n$ in $k$.
--
--   This is the assertion that Drinfeld's special (trace) condition on a quaternionic action — that the trace of $x\in\Lambda$ on the tangent space at each geometric point equals the reduced trace of $x$ — cuts out a simultaneously open and closed locus in the scheme $E$ representing the $\Lambda$-actions on base changes of the polarised abelian surface. It is used in the construction of the Čerednik–Drinfeld model of the Shimura curve, being cited by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_trace_and_exists_isCanonicalPolData_lfp_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_trace_and_exists_isCanonicalPolData_lfp_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_opens_isClosed_range_subset_iff_trace.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    {E : Scheme.{0}} {πE : E ⟶ Spec (CommRingCat.of R)}
    {cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}
    (hE : RepresentsLatticeActions Λ X.L E πE cl) :
    ∃ U : E.Opens, IsClosed (U : Set E) ∧
      ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        (Set.range (cl R' φ L' g hg i').1.base ⊆ (U : Set E) ↔
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k)
              (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
              Function.Injective τ →
              (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
              (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
              (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
              ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
              ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
                LinearMap.trace k V Φ = (n : k))) := by sorry
