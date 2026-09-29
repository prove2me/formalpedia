-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/5cd3e201-da42-5bee-bd78-392e98e3cf98
-- title:
--   Unique lift of an isomorphism of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$, together with a map $\mathrm{coord}:\Lambda\to W(\mathbb{F}_{q^2})^2$ satisfying `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, has dense image modulo every power of $q$, satisfies the twisted multiplication rule in which the second coordinate is composed with Witt-vector Frobenius, and is compatible with reduced traces; assume $1\in\Lambda$. Let $B$ be a Noetherian commutative ring and $B_0$ a $B$-algebra such that $B\to B_0$ is surjective with nilpotent kernel, with $q$ nilpotent in $B$ and $N$ a unit in $B$. Let $E,E'$ be fake elliptic curves over $B$ for $(\Lambda,N)$, let $X,X'$ be formal $\mathcal{O}_D$-modules over $B$ (two-dimensional commutative formal groups with a $W(\mathbb{F}_{q^2})$-action and a uniformiser series $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ[\alpha]=[\alpha^{\sigma}]\circ\varpi$), and let $\theta,\theta'$ be systems of formal coordinates of dimension $2$ along the unit sections of $E,E'$ exhibiting $X,X'$ as the formal groups of $E,E'$ compatibly with the $\Lambda$-actions through $\mathrm{coord}$ (the predicates `IsFormalModuleVia`). Let $E_0,E_0'$ be fake elliptic curves over $B_0$ and $g:E_0.A\to E.A$, $g':E_0'.A\to E'.A$ morphisms exhibiting $E_0,E_0'$ as the pullbacks of $E,E'$ along $\operatorname{Spec}(B_0)\to\operatorname{Spec}(B)$, compatibly with group laws, $\Lambda$-actions and level structures. Let $e_0:E_0.A\cong E_0'.A$ be an isomorphism over $B_0$ (commuting with the structure morphisms) which is a homomorphism for the relative group laws, commutes with the $\Lambda$-actions, and matches the level structures, in the sense that a point factors through $E_0.\mathrm{lev}$ if and only if its image factors through $E_0'.\mathrm{lev}$. Let $T:X\to X'$ be an isomorphism of formal $\mathcal{O}_D$-modules whose reduction agrees with $e_0$: for every ring $B''$ that is an algebra over both $B$ and $B_0$ compatibly, every ideal $J$ with $J^{n+1}=0$, every $s:\mathrm{Fin}\,2\to J$ and every $B''$-point $p_0$ of $E_0$ with $p_0$ followed by $g$ equal to $\theta(B'',s)$, the point $p_0$ followed by $e_0$ and $g'$ equals $\theta'(B'', (\mathrm{nilEval}_n(T_i)(s))_i)$. Then there is exactly one isomorphism $e:E.A\cong E'.A$ such that $g$ followed by $e$ equals $e_0$ followed by $g'$ and, for some (hence any) proof that $e$ commutes with the structure morphisms to $\operatorname{Spec}(B)$, $e$ is a homomorphism for the relative group laws, commutes with the $\Lambda$-actions, matches the level structures in the above factorisation sense, and induces $T$ on formal coordinates: for every $B$-algebra $B''$, ideal $J$ with $J^{n+1}=0$ and $s:\mathrm{Fin}\,2\to J$, the point $\theta(B'',s)$ followed by $e$ equals $\theta'(B'',(\mathrm{nilEval}_n(T_i)(s))_i)$.
--
--   This is the isomorphism half of the Serre–Tate dictionary for fake elliptic curves over a nilpotent thickening: rigidity makes the lift of $e_0$ unique, and the datum of the formal $\mathcal{O}_D$-module isomorphism $T$ makes it exist. It is used in the construction of rigidified isomorphisms between fake elliptic curves with prescribed reduction and in the assembly of the full Serre–Tate dictionary for the deformation functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B)) (hN : IsUnit ((N : ℕ) : B))
    (E E' : FakeEllipticCurve Λ N B) (X X' : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2)
    (hE : E.IsFormalModuleVia coord X θ) (hE' : E'.IsFormalModuleVia coord X' θ')
    (E₀ E₀' : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A) (g' : E₀'.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀ g) (hg' : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E' E₀' g')

    (e₀ : E₀.A ≅ E₀'.A) (he₀f : e₀.hom ≫ E₀'.f = E₀.f)
    (he₀mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt e₀.hom he₀f (E₀.L.mul t P Q) = E₀'.L.mul t (mapPt e₀.hom he₀f P) (mapPt e₀.hom he₀f Q))
    (he₀act : ∀ x : ↥Λ, E₀.act x ≫ e₀.hom = e₀.hom ≫ E₀'.act x)
    (he₀lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P ↔ FactorsThrough E₀'.lev (mapPt e₀.hom he₀f P))

    (T : FormalODModule.Hom X X') (hT : T.IsIso)
    (hTe₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') E₀.f, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ e₀.hom ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) :
    ∃! e : E.A ≅ E'.A, g ≫ e.hom = e₀.hom ≫ g' ∧
      ∃ he : e.hom ≫ E'.f = E.f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom he P)) ∧
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            (θ B'' s).1 ≫ e.hom = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) := by sorry
