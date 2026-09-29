-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/44e4a201-f196-5443-9527-d1af7cd76c15
-- title:
--   Serre–Tate lifting of homomorphisms of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$, together with a map $\mathrm{coord}:\Lambda\to\mathbb{Z}_{q^2}\times\mathbb{Z}_{q^2}$ (values in $W(\mathbb{F}_{q^2})^2$) satisfying `IsOrderCoord`: additive, injective, sending $1$ to $(1,0)$, multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+q\beta\,\varphi(\beta'),\alpha\beta'+\beta\,\varphi(\alpha'))$, with dense image modulo every power of $q$ and with first coordinate computing reduced traces; assume $1\in\Lambda$. Let $B$ be a Noetherian commutative ring with $q$ nilpotent in $B$, and $B_0$ a $B$-algebra with $B\to B_0$ surjective with nilpotent kernel. Let $E,E'$ be fake elliptic curves over $B$ for $(\Lambda,N)$ (two-dimensional abelian schemes with commutative relative group law and $\Lambda$-action), $X,X'$ formal $\mathcal{O}_D$-modules over $B$ of height data recorded by `FormalODModule q B` (two-dimensional commutative formal groups with $\mathbb{Z}_{q^2}$-action and uniformiser $\varpi$, $\varpi\circ\varpi=[q]$, $\varpi\circ[\alpha]=[\varphi(\alpha)]\circ\varpi$), and $\theta,\theta'$ formal coordinates of dimension $2$ for $E,E'$ which exhibit $X,X'$ as their formal modules compatibly with $\mathrm{coord}$ (`IsFormalModuleVia`). Let $E_0,E_0'$ be fake elliptic curves over $B_0$ and $g,g'$ morphisms exhibiting them as pullbacks of $E,E'$ along $\operatorname{Spec}B_0\to\operatorname{Spec}B$ in the sense of `IsPullbackVia` (pullback square, compatibility with the group laws and the $\Lambda$-actions, and factorisation of infinitesimal points through the level structure). Let $\varphi_0:E_0\to E_0'$ be a morphism over $B_0$ which is a homomorphism for the relative group laws on all test schemes and commutes with the $\Lambda$-actions, and let $T:X\to X'$ be a homomorphism of formal $\mathcal{O}_D$-modules whose truncated evaluations compute $\varphi_0$ on nilpotent formal points: for every ring $B''$ that is a $B$- and $B_0$-algebra compatibly, every ideal $J$ with $J^{n+1}=0$, every $s:\{0,1\}\to J$, and every point $p_0$ of $E_0$ over $\operatorname{Spec}B''$ with $p_0\circ g$ equal to $\theta(B'')(s)$, the composite of $p_0$ with $\varphi_0$ followed by $g'$ equals $\theta'(B'')\bigl(\mathrm{nilEval}_n(T_i)(s)\bigr)$. Then there is exactly one morphism $\varphi:E.A\to E'.A$ with $g$ followed by $\varphi$ equal to $\varphi_0$ followed by $g'$, which lies over $\operatorname{Spec}B$, is a homomorphism for the relative group laws on all test schemes, satisfies $E.\mathrm{act}(x)$ followed by $\varphi$ equals $\varphi$ followed by $E'.\mathrm{act}(x)$ for all $x\in\Lambda$, and induces $T$ on formal coordinates: for every $B$-algebra $B''$, ideal $J$ with $J^{n+1}=0$ and $s$ valued in $J$, $\theta(B'')(s)$ followed by $\varphi$ equals $\theta'(B'')\bigl(\mathrm{nilEval}_n(T_i)(s)\bigr)$.
--
--   This is the Serre–Tate lifting theorem for homomorphisms in the form needed for fake elliptic curves at a prime ramified in the quaternion algebra: along a nilpotent thickening $B\to B_0$, a $\Lambda$-equivariant homomorphism of the reductions lifts uniquely once a lift of the induced map of formal $\mathcal{O}_D$-modules is prescribed, the ramification being encoded in the coordinate map `coord`. It is used to lift isomorphisms ([`CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_iso_lift_of_isFormalModuleVia_of_one_mem)) in the Čerednik–Drinfeld description of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B))
    (E E' : FakeEllipticCurve Λ N B) (X X' : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2)
    (hE : E.IsFormalModuleVia coord X θ) (hE' : E'.IsFormalModuleVia coord X' θ')
    (E₀ E₀' : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A) (g' : E₀'.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀ g) (hg' : FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E' E₀' g')

    (φ₀ : E₀.A ⟶ E₀'.A) (hφ₀ : φ₀ ≫ E₀'.f = E₀.f)
    (φ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt φ₀ hφ₀ (E₀.L.mul t P Q) = E₀'.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))
    (φ₀_act : ∀ x : ↥Λ, E₀.act x ≫ φ₀ = φ₀ ≫ E₀'.act x)

    (T : FormalODModule.Hom X X')
    (hTφ₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') E₀.f, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ φ₀ ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) :
    ∃! φ : E.A ⟶ E'.A, g ≫ φ = φ₀ ≫ g' ∧
      ∃ hφ : φ ≫ E'.f = E.f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            (θ B'' s).1 ≫ φ = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toSeries i) s)).1) := by sorry
