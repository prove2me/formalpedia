-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_isFinite_degeneracy
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.isFinite_degeneracy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/1c20c770-d7b8-505d-bb03-de79b364aca3
-- title:
--   Finiteness of the two ℓ-degeneracy morphisms
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N \neq 0$, and let $\ell$ be a prime. Let $f : \mathcal{X} \to \operatorname{Spec}\overline{\mathbb{Q}}$ together with an assignment `pt`, sending a commutative ring $S$, a morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\overline{\mathbb{Q}}$ and a fake elliptic curve over $S$ with $\Lambda$-action and level $N$ to a morphism $\operatorname{Spec} S \to \mathcal{X}$ over $s$, satisfy `IsCoarseModuli`: `pt` is constant on isomorphism classes, compatible with pullback along ring homomorphisms, bijective up to isomorphism on points valued in algebraically closed fields, and universal among such assignments; assume $\mathcal{X}$ integral and $f$ separated and locally of finite type. Let $g : \mathcal{Y} \to \operatorname{Spec}\overline{\mathbb{Q}}$ with `ptT` satisfy the corresponding `IsCoarseModuliT` conditions for pairs consisting of such a curve together with an extra level structure at $\ell$, with $\mathcal{Y}$ integral and $g$ separated and locally of finite type. Let $d_0, d_1 : \mathcal{Y} \to \mathcal{X}$ be morphisms over $\overline{\mathbb{Q}}$ ($d_i$ followed by $f$ equals $g$) such that, for all $S$, $s$ and every pair $u$, the point $\mathrm{ptT}(u)$ followed by $d_0$ is $\mathrm{pt}$ of the underlying curve $u.1$, and $\mathrm{ptT}(u)$ followed by $d_1$ is $\mathrm{pt}(d)$ whenever `IsLevelIsogeny` holds for $u$ and a curve $d$, i.e. there are morphisms $\varphi : u.1.A \to d.A$ and $\psi$ back over $S$, compatible with the group laws and the $\Lambda$-actions, whose composites are the action of $\ell$ when $\ell \in \Lambda$, with $\varphi$ killing exactly the points factoring through the $\ell$-level subscheme $u.2.\mathrm{levK}$ and carrying level-$N$ points to level-$N$ points. Then $d_0$ and $d_1$ are finite morphisms.
--
--   This is the statement that the two degeneracy maps from the coarse moduli curve of fake elliptic curves with an extra level structure at $\ell$ down to the coarse moduli curve of fake elliptic curves — forgetting the $\ell$-structure, respectively dividing by it — are finite. It is used in the construction of a moduli tower witness over $\overline{\mathbb{Q}}$, where finiteness over a proper base makes $\mathcal{Y}$ proper and hence every place of its function field a moduli point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_isFinite_degeneracy.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.IsCoarseModuliT.isFinite_degeneracy
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt) [IsIntegral 𝒳] [IsSeparated f] [LocallyOfFiniteType f]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (h𝒴 : IsCoarseModuliT Λ N ℓ 𝒴 g ptT) [IsIntegral 𝒴] [IsSeparated g] [LocallyOfFiniteType g]
    (d₀ d₁ : 𝒴 ⟶ 𝒳) (hd₀g : d₀ ≫ f = g) (hd₁g : d₁ ≫ f = g)
    (hd₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptT S s u).1 ≫ d₀ = (pt S s u.1).1)
    (hd₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny ℓ u d → (ptT S s u).1 ≫ d₁ = (pt S s d).1) :
    IsFinite d₀ ∧ IsFinite d₁ := by sorry
