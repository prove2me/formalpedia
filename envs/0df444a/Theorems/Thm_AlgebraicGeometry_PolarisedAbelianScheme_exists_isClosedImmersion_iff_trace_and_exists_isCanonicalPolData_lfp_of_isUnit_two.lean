-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_trace_and_exists_isCanonicalPolData_lfp_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_trace_and_exists_isCanonicalPolData_lfp_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/3098991a-7073-5f7c-b2b0-dbc780b0ef21
-- title:
--   Trace and canonical-cube conditions cut out a closed subscheme
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$, and let $\beta:\mathrm{Fin}\,4\to\Lambda$ be such that every element of $\Lambda$ is uniquely an integral combination $\sum_j c_j\beta_j$. Let $d,m$ be naturals with $m\ge 3$, let $R$ be a commutative ring in which $m$ and $2$ are units, and let $X$ be a polarised abelian scheme over $R$ of relative fibre dimension $2$, with level-$m$ structure given by $4$ $m$-torsion sections spanning the geometric $m$-torsion freely, and with invertible, very ample polarisation module `X.pol` of geometric fibre $H^0$-rank $d$. Let $\pi_E:E\to\operatorname{Spec}R$ together with the assignment `cl`, sending a ring map $\varphi:R\to R'$, a group-law pullback $g$ of $(X.A,X.L)$ along $\varphi$ and a $\Lambda$-action on it to a section of $\pi_E$ over $\operatorname{Spec}\varphi$, represent the $\Lambda$-actions on base changes of `X.L`, in the sense of `RepresentsLatticeActions` (compatibility with further base change, surjectivity and injectivity of `cl`). The conclusion asserts the existence of a scheme $Z_2$ and a morphism $\iota:Z_2\to E$ which is a closed immersion and locally of finite presentation, such that for every $R'$, every $\varphi:R\to R'$, every $(A',f',L')$ with a group pullback $g$ of `X.L` along $\varphi$ and every lattice action $i'$ of $\Lambda$ on $(f',L')$, the classifying section $\mathrm{cl}\,R'\,\varphi\,L'\,g\,i'$ factors through $\iota$ (there is $y:\operatorname{Spec}R'\to Z_2$ with $y$ followed by $\iota$ equal to it) if and only if both of the following hold. First, the trace condition: for every algebraically closed field $k$ with a ring map $sk:R'\to k$, every finite-dimensional $k$-vector space $V$ and every injective $\tau:V\to$ points of $f'$ over the dual-number base `tangentBase k sk` whose image is exactly the set of tangent vectors of $L'$, which is additive for `L'.mul` and compatible with scalars via `tangentScale`, and for every $x\in\Lambda$ and $k$-linear $\Phi$ on $V$ with $\tau(\Phi v)$ the pushforward of $\tau v$ along $i'.\mathrm{act}\,x$, one has $\operatorname{tr}_k\Phi=n$ in $k$ for every integer $n$ with $x+\bar x=n$. Second, there is a module `polE` on $A'$ which is a canonical polarisation datum for $f'$, $L'$, the action of $i'$ and $\mathrm{star}$ in the sense of `IsCanonicalPolData` — invertible, `IsSymmetric`, with `KernelIsTwoTorsion`, with strictly positive geometric fibre $H^0$-rank, becoming locally on the base a product $\mathcal{L}_0\otimes[-1]^{*}\mathcal{L}_0$ with `KernelTrivial` $\mathcal{L}_0$ after some faithfully flat base change, and `RosatiCompatible` with the action and $\mathrm{star}$ — such that $g^{*}$`X.pol` and `polE`$^{\otimes 3}$ are isomorphic locally on $\operatorname{Spec}R'$, in the sense of `LocIsoOnBase`.
--
--   This is the step, in the construction of the moduli schemes attached to a maximal order in an indefinite quaternion algebra ramified exactly at $q$ and $q'$, which shows that Drinfeld's trace condition together with the requirement that the given polarisation be, locally on the base, the cube of a canonical polarisation datum for the quaternionic action defines a closed, finitely presented subscheme of the scheme $E$ representing lattice actions. It is the edition used when $2$ is invertible on the base, and it is cited in the further refinement that also imposes the existence of a level generator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_trace_and_exists_isCanonicalPolData_lfp_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_trace_and_exists_isCanonicalPolData_lfp_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (h2 : IsUnit (2 : R)) (X : PolarisedAbelianScheme 2 d m R)
    {E : Scheme.{0}} {πE : E ⟶ Spec (CommRingCat.of R)}
    {cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}
    (hE : RepresentsLatticeActions Λ X.L E πE cl) :
    ∃ (Z₂ : Scheme.{0}) (ι : Z₂ ⟶ E), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        ((∃ y : Spec (CommRingCat.of R') ⟶ Z₂, y ≫ ι = (cl R' φ L' g hg i').1) ↔
          ((∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k)
              (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
              Function.Injective τ →
              (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
              (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
              (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
              ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
              ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
                LinearMap.trace k V Φ = (n : k)) ∧
           (∃ polE : A'.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f' L' i'.act i'.act_over star polE ∧
              LocIsoOnBase f' ((Scheme.Modules.pullback g).obj X.pol) (polE ⊗ polE ⊗ polE)))) := by sorry
