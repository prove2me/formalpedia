-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b6f5c412-2482-56d4-9fc8-21d05cc5e2d5
-- title:
--   Atkin–Lehner lift fixes the generic point of the geometric fibre
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q, q'$ with $q' \neq q$, and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $r$ be a prime with $r = q$ or $r = q'$, and assume $r \nmid N$, $q \nmid N$, $q' \nmid N$. Let $\mathcal{O}_0$ be a commutative ring, $f_0 : \mathcal{X}_0 \to \operatorname{Spec} \mathcal{O}_0$ a morphism locally of finite type, and $\mathrm{pt}_0$ an assignment sending each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec} \mathcal{O}_0$ and each fake elliptic curve $E$ over $S$ (for $\Lambda$ and level $N$) to a morphism $\operatorname{Spec} S \to \mathcal{X}_0$ over $s$, such that `IsCoarseModuli` holds: invariance under isomorphism of fake elliptic curves, compatibility with base change along ring maps, bijectivity on isomorphism classes over algebraically closed fields, and the universal property among such $\mathcal{O}_0$-schemes with points. Let $ar : \mathcal{X}_0 \to \mathcal{X}_0$ satisfy: whenever $E'$ is an Atkin–Lehner quotient of $E$ at $r$ (in the sense of the predicate `FakeEllipticCurve.IsAtkinLehnerQuotient`, given by a pair of mutually $r$-multiplying $\Lambda$-equivariant homomorphisms compatible with level structures), the moduli point of $E$ followed by $ar$ is the moduli point of $E'$. Let $K$ be an algebraically closed field of characteristic zero with $s_K : \operatorname{Spec} K \to \operatorname{Spec} \mathcal{O}_0$, and assume the fibre product $\mathcal{X}_0 \times_{\operatorname{Spec} \mathcal{O}_0} \operatorname{Spec} K$ is integral. Then every endomorphism $a_K$ of that fibre product satisfying $a_K$ followed by the first projection equals the first projection followed by $ar$, and $a_K$ followed by the second projection equals the second projection, fixes the generic point: the underlying continuous map of $a_K$ sends the generic point to itself.
--
--   This is the step showing that a lift to the geometric generic fibre of the Atkin–Lehner involution on a coarse moduli scheme of fake elliptic curves is dominant, so that it induces an automorphism of the function field. It is used in the read-off of the Mumford embedding in the Čerednik–Drinfeld description of the Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd.lean

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
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuli.base_genericPoint_eq_of_comp_fst_eq_fst_comp_of_isAtkinLehnerQuotient_of_not_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (r : ℕ) [Fact r.Prime] (hr : r = q ∨ r = q') (hrN : ¬ r ∣ N)

    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)

    (𝒪₀ : Type) [CommRing 𝒪₀]
    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [LocallyOfFiniteType f₀]
    (ar : 𝒳₀ ⟶ 𝒳₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)

    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (sK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of 𝒪₀))
    [hXKint : IsIntegral (Limits.pullback f₀ sK)]
    :
    ∀ (aK : Limits.pullback f₀ sK ⟶ Limits.pullback f₀ sK),
      aK ≫ Limits.pullback.fst f₀ sK = Limits.pullback.fst f₀ sK ≫ ar →
      aK ≫ Limits.pullback.snd f₀ sK = Limits.pullback.snd f₀ sK →
      aK.base (genericPoint ((Limits.pullback f₀ sK) : Scheme.{0})) = genericPoint ((Limits.pullback f₀ sK) : Scheme.{0}) := by sorry
