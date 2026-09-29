-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lift_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed_of_one_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_lift_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed_of_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d4974190-84a9-5637-9ed7-0cc2ebeb3486
-- title:
--   Serre–Tate lifting of fake elliptic curves, Artinian local base
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ containing $1$, a natural number $N$ and a prime $q$, together with a map $\mathrm{coord}:\Lambda\to W(\mathbb{F}_{q^2})\times W(\mathbb{F}_{q^2})$ satisfying `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, has dense image modulo every power of $q$, satisfies the twisted multiplication rule $\mathrm{coord}(mm')=(\alpha\alpha'+q\beta\,\varphi(\beta'),\ \alpha\beta'+\beta\,\varphi(\alpha'))$ with $\varphi$ the Witt-vector Frobenius, and matches reduced traces: $m+\bar m=n$ forces $\alpha+\varphi(\alpha)=n$. Let $B$ be a commutative Artinian local ring with algebraically closed residue field in which $q$ is nilpotent and $N$ is a unit, and let $B_0$ be a commutative $B$-algebra with $B\to B_0$ surjective with nilpotent kernel. Let $E_0$ be a fake elliptic curve over $B_0$ of type $(\Lambda,N)$, let $X$ be a formal $\mathcal{O}_D$-module over $B$ for $q$ (a commutative two-dimensional formal group law with $W(\mathbb{F}_{q^2})$-action and uniformiser series $\varpi$ satisfying $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\varphi(a)]\circ\varpi$), and let $\theta_0$ be formal coordinates in two variables for $E_0.f$ exhibiting $X\otimes_B B_0$ as the formal module of $E_0$ via $\mathrm{coord}$. Then there exist a fake elliptic curve $E$ over $B$ of type $(\Lambda,N)$, a morphism $g:E_0.A\to E.A$ and formal coordinates $\theta$ for $E.f$ such that: $g$ exhibits $E_0$ as the pull-back of $E$ along $B\to B_0$ (the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}$ of $B\to B_0$ is a pullback, $g$ carries the group law of $E_0$ to that of $E$, satisfies $E_0.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x\in\Lambda$, and points factoring through the level structure of $E_0$ arise from $E.C$); $\theta$ exhibits $X$ as the formal module of $E$ via $\mathrm{coord}$; and for every $B''$ that is an algebra over both $B$ and $B_0$ compatibly, and every tuple $s:\mathrm{Fin}\,2\to B''$ of nilpotents, $\theta_0(B'',s)$ followed by $g$ equals $\theta(B'',s)$.
--
--   This is the essential-surjectivity half of the Serre–Tate theorem in the form needed for fake elliptic curves at a prime $q$ dividing the discriminant: deformations of $E_0$ along a nilpotent surjection are produced from deformations of its formal $\mathcal{O}_D$-module, the base being Artinian local with algebraically closed residue field. It is the edition consumed at such points in the construction of the Serre–Tate dictionary and in the rigidified pull-back and Rosati-compatibility statements of the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lift_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed_of_one_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_lift_of_isFormalModuleVia_of_isArtinianRing_of_isAlgClosed_of_one_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)

    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B)) (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (X : FormalODModule q B) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (h₀ : E₀.IsFormalModuleVia coord (X.map (algebraMap B B₀)) θ₀) :
    ∃ (E : FakeEllipticCurve Λ N B) (g : E₀.A ⟶ E.A) (θ : RelativeGroupLaw.FormalCoordinates E.f 2),
      FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀ g ∧
      E.IsFormalModuleVia coord X θ ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B''] (s : Fin 2 → B''),
        (∀ i, IsNilpotent (s i)) → (θ₀ B'' s).1 ≫ g = (θ B'' s).1 := by sorry
