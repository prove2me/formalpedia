-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_base_genericPoint_eq_of_comp_fst_eq_fst_comp_degeneracy
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.base_genericPoint_eq_of_comp_fst_eq_fst_comp_degeneracy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ffc6f9b8-cc1f-54d8-ae85-6ee2dfda1628
-- title:
--   Lifted degeneracy maps are dominant on geometric generic fibres
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$; let $\Lambda$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $N \neq 0$, and let $\ell$ be a prime distinct from $q$ and $q'$. Over a commutative ring $\mathcal{O}_0$ one is given: a scheme $\mathcal{X}_0$ with a morphism $f_0$ to $\operatorname{Spec}\mathcal{O}_0$, locally of finite type, together with a point assignment $\mathrm{pt}_0$ sending each fake elliptic curve with $\Lambda$-action and level $N$ over an $\mathcal{O}_0$-algebra $S$ to a morphism over the structure map, such that `IsCoarseModuli` holds (invariance under isomorphism, compatibility with base change along ring maps, bijectivity of $\mathrm{pt}_0$ on points with values in algebraically closed fields, and the universal property among such point assignments); and a scheme $\mathcal{Y}$ with $g : \mathcal{Y} \to \operatorname{Spec}\mathcal{O}_0$ and $\mathrm{pt}_T$ defined on pairs consisting of a fake elliptic curve and an extra $\ell$-level structure, satisfying the corresponding predicate `IsCoarseModuliT`. Two morphisms $d_0, d_1 : \mathcal{Y} \to \mathcal{X}_0$ are assumed to realise the two degeneracy maps on points: $\mathrm{pt}_T(u)$ followed by $d_0$ equals $\mathrm{pt}_0$ of the underlying curve $u.1$, and $\mathrm{pt}_T(u)$ followed by $d_1$ equals $\mathrm{pt}_0(d)$ whenever `FakeEllipticCurve.IsLevelIsogeny ℓ u d` holds. Finally let $K$ be an algebraically closed field of characteristic zero with a map $s_K : \operatorname{Spec} K \to \operatorname{Spec}\mathcal{O}_0$, and assume both fibre products $\mathcal{X}_0 \times_{\mathcal{O}_0} K$ and $\mathcal{Y} \times_{\mathcal{O}_0} K$ are integral schemes. The conclusion: for each $k \in \{0,1\}$ and each morphism $d_K$ between these fibre products whose composite with the first projection equals the first projection followed by $d_0$ (if $k = 0$) or $d_1$ (otherwise), and whose composite with the second projection is the second projection, the underlying continuous map of $d_K$ sends the generic point of $\mathcal{Y} \times_{\mathcal{O}_0} K$ to the generic point of $\mathcal{X}_0 \times_{\mathcal{O}_0} K$.
--
--   This records that the two degeneracy maps between the coarse moduli of fake elliptic curves with level $N$ and with an extra $\ell$-level structure, base changed to a geometric fibre, are dominant in the strongest pointwise sense: each sends the generic point to the generic point. It is used in the Čerednik–Drinfeld part of the development, where degeneracy maps are traced through function fields and through the Mumford embedding.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_base_genericPoint_eq_of_comp_fst_eq_fst_comp_degeneracy.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuliT.base_genericPoint_eq_of_comp_fst_eq_fst_comp_degeneracy
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')

    (𝒪₀ : Type) [CommRing 𝒪₀]
    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [LocallyOfFiniteType f₀]
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of 𝒪₀))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (h𝒴 : IsCoarseModuliT Λ N ℓ 𝒴 g ptT)
    (d₀ d₁ : 𝒴 ⟶ 𝒳₀)
    (hd₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptT S s u).1 ≫ d₀ = (pt₀ S s u.1).1)
    (hd₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny ℓ u d → (ptT S s u).1 ≫ d₁ = (pt₀ S s d).1)

    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (sK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of 𝒪₀))
    [hXKint : IsIntegral (Limits.pullback f₀ sK)] [hYKint : IsIntegral (Limits.pullback g sK)]
    :
    ∀ (k : Fin 2) (dK : Limits.pullback g sK ⟶ Limits.pullback f₀ sK),
      dK ≫ Limits.pullback.fst f₀ sK = Limits.pullback.fst g sK ≫ (if k = 0 then d₀ else d₁) →
      dK ≫ Limits.pullback.snd f₀ sK = Limits.pullback.snd g sK →
      dK.base (genericPoint ((Limits.pullback g sK) : Scheme.{0})) = genericPoint ((Limits.pullback f₀ sK) : Scheme.{0}) := by sorry
