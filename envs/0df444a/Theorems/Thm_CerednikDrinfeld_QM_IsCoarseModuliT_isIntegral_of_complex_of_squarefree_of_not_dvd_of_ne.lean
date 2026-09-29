-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_isIntegral_of_complex_of_squarefree_of_not_dvd_of_ne
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_complex_of_squarefree_of_not_dvd_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7279ba17-7ff0-5298-b9b4-aa542b8b5d89
-- title:
--   Integrality of the complex coarse moduli scheme with extra level at ℓ
-- statement:
--   Let $q\neq q'$ be primes and let $a,b\in\mathbb{Q}$ be such that $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for every $v$ in the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ the completion $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element a unit) precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $N\geq 1$ be squarefree with $q\nmid N$, $q'\nmid N$, and let $\ell$ be a prime with $\ell\nmid N$, $\ell\neq q$, $\ell\neq q'$. Let $R\leq\Lambda$ be an Eichler order of level $N$, i.e. an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders with relative index $N$ in $\Lambda_1$, and let $\iota:B\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism. Let $f:\mathcal{X}\to\operatorname{Spec}\mathbb{C}$ be a scheme over $\mathbb{C}$ together with an assignment `pt` sending each commutative ring $S$, each morphism $s:\operatorname{Spec} S\to\operatorname{Spec}\mathbb{C}$ and each pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure together with an extra level structure at $\ell$ (a closed subgroup scheme, finite flat of fibre rank $\ell^2$, $\Lambda$-stable, disjoint from the level-$N$ structure, geometrically isomorphic to $(\mathbb{Z}/\ell)^2$) to a morphism $\operatorname{Spec} S\to\mathcal{X}$ over $s$; assume `IsCoarseModuliT`, i.e. `pt` is constant on isomorphism classes, compatible with base change along pullbacks of pairs, bijective on isomorphism classes of pairs over algebraically closed fields, and universal among such point assignments. Assume furthermore that $f$ is separated, quasi-compact, locally of finite type and smooth of relative dimension $1$. Then $\mathcal{X}$ is integral.
--
--   This is the integrality (irreducibility and reducedness) of the complex Shimura curve coarse moduli scheme for fake elliptic curves with level-$N$ structure and an additional level structure at a prime $\ell$ prime to $N$, $q$ and $q'$. It feeds the construction of integral models with $\Gamma_0(N)\cap\Gamma^0(\ell)$-type level over algebraically closed fields of characteristic zero used later in the Čerednik–Drinfel'd comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_isIntegral_of_complex_of_squarefree_of_not_dvd_of_ne.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_complex_of_squarefree_of_not_dvd_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (ℓ : ℕ) (hℓ : ℓ.Prime)

    (hℓN : ¬ ℓ ∣ N) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')

    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of ℂ))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuliT Λ N ℓ 𝒳 f pt)
    (hsep : IsSeparated f) (hqc : QuasiCompact f) (hlft : LocallyOfFiniteType f) (hsm : SmoothOfRelativeDimension 1 f) :
    IsIntegral 𝒳 := by sorry
