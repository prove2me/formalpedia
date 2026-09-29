-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/9582ba7c-26a8-5a1e-a448-c7097c89cc51
-- title:
--   Integral geometric fibre of a coarse pairs model over ℤ[1/M]
-- statement:
--   Let $q\neq q'$ be primes and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among the orders containing it, let $N\geq 1$ be squarefree with $q\nmid N$ and $q'\nmid N$, let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$, and let $M\geq 1$ be such that in $\Lambda$-free terms the images of $N$, $\ell$, $2$, $3$ and of some $m_0\geq 3$ divisible by $\ell$ are units in $R_M:=$ `Localization.Away ((M : ℕ) : ℤ)`. Let $X$ be a scheme and $\pi_X:X\to\operatorname{Spec}R_M$ a morphism, together with a point-law $\mathrm{pt}$ assigning to each commutative ring $S$, each $s:\operatorname{Spec}S\to\operatorname{Spec}R_M$ and each pair in `FakeEllipticCurve.WithExtraLevel Λ N ℓ S` (a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure, equipped with an `ExtraLevel ℓ` datum: a closed subscheme of the abelian scheme, finite flat of fibre rank $\ell^2$, killed by $\ell$, stable under $\Lambda$, disjoint from the level structure and geometrically isomorphic to $(\mathbb{Z}/\ell)^2$) a morphism $\operatorname{Spec}S\to X$ over $s$. Assume `IsCoarseModuliT Λ N ℓ X πX pt`, i.e. $\mathrm{pt}$ is constant on isomorphism classes, compatible with pullback of pairs along ring homomorphisms, bijective on isomorphism classes over algebraically closed fields, and universal among such point-laws; assume further that $\pi_X$ is separated, quasi-compact, locally of finite type, flat, proper and smooth of relative dimension $1$. Then there exist a type $C$ with a field structure that is algebraically closed of characteristic zero and a morphism $s_C:\operatorname{Spec}C\to\operatorname{Spec}R_M$ such that the fibre product $X\times_{\operatorname{Spec}R_M}\operatorname{Spec}C$ is an integral scheme.
--
--   The statement records that a coarse model over $\mathbb{Z}[1/M]$ of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q,q'$, with level $N$ and extra level structure at $\ell$, has at least one integral geometric fibre in characteristic zero. It feeds the characteristic-zero input for [`CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_isAlgClosed_of_not_dvd_of_squarefree_of_ne), where integrality over an arbitrary algebraically closed base is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuliT.exists_isIntegral_pullback_of_isAlgClosed_charZero_of_not_dvd_of_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hNsq : Squarefree N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (M : ℕ) [NeZero M]
    (hN : IsUnit ((N : ℕ) : Localization.Away ((M : ℕ) : ℤ))) (hℓu : IsUnit ((ℓ : ℕ) : Localization.Away ((M : ℕ) : ℤ)))
    (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hℓm₀ : ℓ ∣ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : Localization.Away ((M : ℕ) : ℤ)))
    (h2 : IsUnit ((2 : ℕ) : Localization.Away ((M : ℕ) : ℤ))) (h3 : IsUnit ((3 : ℕ) : Localization.Away ((M : ℕ) : ℤ)))
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt) (hsep : IsSeparated πX) (hqc : QuasiCompact πX) (hlft : LocallyOfFiniteType πX)
    (hflat : Flat πX) (hproper : IsProper πX) (hsmooth : SmoothOfRelativeDimension 1 πX) :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C)
      (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ)))),
      IsIntegral (Limits.pullback πX sC) := by sorry
