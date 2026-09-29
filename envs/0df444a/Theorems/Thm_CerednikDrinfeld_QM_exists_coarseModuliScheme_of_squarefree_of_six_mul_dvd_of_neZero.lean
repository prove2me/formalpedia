-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_coarseModuliScheme_of_squarefree_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.QM.exists_coarseModuliScheme_of_squarefree_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/77a3c18a-f39e-5ecc-86e1-c81b14633a92
-- title:
--   Coarse moduli scheme of fake elliptic curves over ℤ[1/D]
-- statement:
--   Let $N$ be a non-zero natural number, $q$ and $q'$ primes with $q' \neq q$, neither dividing $N$, and let $N$ be squarefree. Let $a,b \in \mathbb Q$ be such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all non-zero elements invertible exactly when $q \in v$ or $q' \in v$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule that is an order, maximal among the orders containing it, and let $D$ be a non-zero natural number divisible by $6Nqq'$. Write $\mathcal O = \mathbb Z[1/D]$ for `Localization.Away` of $D$ in $\mathbb Z$. Then there exist an integral scheme $X$, a morphism $\pi_X : X \to \operatorname{Spec} \mathcal O$, and an assignment `pt` sending each commutative ring $S$, each $\mathcal O$-structure morphism $s : \operatorname{Spec} S \to \operatorname{Spec} \mathcal O$ and each object $E$ of `FakeEllipticCurve Λ N S` (an abelian-scheme datum $A \to \operatorname{Spec} S$ with commutative relative group law, fibres of topological Krull dimension $2$, a $\Lambda$-action satisfying the additivity, multiplicativity and trace conditions, and a level-$N$ datum) to a morphism $\operatorname{Spec} S \to X$ over $s$, such that: $\pi_X$ is smooth and proper; `pt` is constant on `FakeEllipticCurve.Iso`-classes; for every ring homomorphism $\varphi : S \to S'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and every $E$, $E'$ with `FakeEllipticCurve.IsPullback φ E E'`, the point of $E'$ is $\operatorname{Spec}\varphi$ followed by the point of $E$; over every algebraically closed field $k$ with structure morphism $s$, `pt` is surjective onto the $k$-points of $X$ over $s$ and injective up to `FakeEllipticCurve.Iso`; $\pi_X$ is smooth of relative dimension $1$; every pullback of $\pi_X$ along a point of an algebraically closed field is integral; and the function field of $X$ has characteristic zero, with every element algebraic over $\mathbb Q$ lying in the image of $\mathbb Q$.
--
--   This is the construction of the coarse moduli scheme of fake elliptic curves with $\Lambda$-action and level-$N$ structure over $\mathbb Z[1/D]$, the integral model of the Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$, together with its smoothness, properness, geometric integrality and the algebraic closedness of $\mathbb Q$ in its function field. It is the first construction stage used by the Shimura-curve model with Hecke tower and rigid moduli witness, and by the finiteness statement for fake elliptic curves with prescribed non-isomorphic translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_coarseModuliScheme_of_squarefree_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld
open CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_coarseModuliScheme_of_squarefree_of_six_mul_dvd_of_neZero
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hN : Squarefree N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D)
    :
    ∃ (X : Scheme.{0}) (hXint : IsIntegral X)
      (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (pt : ∀ (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
        FakeEllipticCurve Λ N S → SchemeHomOver s πX),
      Smooth πX ∧ IsProper πX ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
    FakeEllipticCurve.Iso E E' → pt S s E = pt S s E') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
    FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
    ∃ E : FakeEllipticCurve Λ N k, pt k s E = P) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
    (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E') ∧

      SmoothOfRelativeDimension 1 πX ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
    IsIntegral (CategoryTheory.Limits.pullback πX s)) ∧

      (∃ hchar : CharZero X.functionField, haveI := hchar;
        ∀ x : X.functionField, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ X.functionField)) := by sorry
