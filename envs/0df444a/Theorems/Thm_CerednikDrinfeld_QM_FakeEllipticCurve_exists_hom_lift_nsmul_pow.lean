-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_lift_nsmul_pow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_lift_nsmul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b8558ba0-d526-5da6-8f87-9ba84316eff1
-- title:
--   Lifting q^{nμ}φ₀ to a homomorphism of fake elliptic curves
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$, together with a map $\mathrm{coord}:\Lambda\to\mathbb{Z}_{q^2}\times\mathbb{Z}_{q^2}$ satisfying `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+q\beta\varphi(\beta'),\alpha\beta'+\beta\varphi(\alpha'))$ with $\varphi$ the Witt-vector Frobenius, is injective, has dense image modulo every power of $q$, and matches reduced traces. Let $B$ be a Noetherian commutative ring and $B_0$ a $B$-algebra with $\mathrm{algebraMap}\,B\,B_0$ surjective and kernel $I$ satisfying $I^{\mu+1}=0$, and suppose $q^n=0$ in $B$. Let $E,E'$ be fake elliptic curves of type $(\Lambda,N)$ over $B$, let $X,X'$ be formal $\mathcal{O}_D$-modules at $q$ over $B$ (two-dimensional commutative formal groups with a $\mathbb{Z}_{q^2}$-action and a uniformiser series), and let $\theta,\theta'$ be two-parameter formal coordinates along the unit sections of $E.f$, $E'.f$, with $E$ a formal module via $(\mathrm{coord},X,\theta)$ and $E'$ via $(\mathrm{coord},X',\theta')$: $\theta$ is a system of formal coordinates for the relative group law with formal group $X.F$, and the $\Lambda$-action on formal points is computed by $\mathrm{addVia}(X.\mathrm{act}\,\alpha,(X.\mathrm{act}\,\beta)\circ X.\varpi)$ for $(\alpha,\beta)=\mathrm{coord}(m)$. Let $E_0,E_0'$ be fake elliptic curves over $B_0$ together with $g:E_0.A\to E.A$, $g':E_0'.A\to E'.A$ exhibiting them as pullbacks along $B\to B_0$ in the sense of `IsPullbackVia` (cartesian square, compatibility with the group laws, with the $\Lambda$-actions, and factorisation of level points). Let $\varphi_0:E_0.A\to E_0'.A$ be a morphism over $B_0$ which is additive on points over every test scheme and commutes with the $\Lambda$-actions, and let $T:X\to X'$ be a homomorphism of formal $\mathcal{O}_D$-modules such that, for every $B$- and $B_0$-algebra $B''$ in a scalar tower, every ideal $J$ with $J^{k+1}=0$, every $s:\mathrm{Fin}\,2\to J$ and every point $p_0$ of $E_0$ over $\mathrm{Spec}\,B''$ with $p_0$ followed by $g$ equal to $\theta\,B''\,s$, the composite of $p_0$ with $\varphi_0$ and then $g'$ equals $\theta'$ evaluated at the truncated values $\mathrm{nilEval}\,k\,(T_i)(s)$. Then there is a morphism $\tilde N:E.A\to E'.A$ over $B$ which is additive on points over every $B$-test scheme, satisfies $E.\mathrm{act}\,x$ followed by $\tilde N$ equals $\tilde N$ followed by $E'.\mathrm{act}\,x$ for all $x\in\Lambda$, reduces to $q^{n\mu}\varphi_0$ in the sense that for every point $P$ of $E_0$ over a $B_0$-test scheme the composite $P$, $g$, $\tilde N$ equals $q^{n\mu}\cdot\varphi_0(P)$ (the iterated sum in $E_0'.L$) followed by $g'$, and on formal coordinates is given by $(\theta\,B''\,s)$ followed by $\tilde N$ equal to $\theta'\,B''$ evaluated at the truncations of the series $(X'.\mathrm{act}\,q^{n\mu})\circ T$ at $s$, for all $B$-algebras $B''$, ideals $J$ with $J^{k+1}=0$ and $s$ with entries in $J$.
--
--   This is the existence half of the homomorphism-lifting step for fake elliptic curves over a nilpotent thickening, in the style of Katz's rigidity lemma for Serre–Tate local moduli: a $\Lambda$-equivariant homomorphism between the reductions, together with a compatible homomorphism of the attached formal $\mathcal{O}_D$-modules, lifts after multiplication by $q^{n\mu}$. It is used to obtain the unique lift statement [`CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_lift_of_isFormalModuleVia_of_one_mem), in the deformation-theoretic input to the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_lift_nsmul_pow.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_lift_nsmul_pow
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (n : ℕ) (hn : ((q : ℕ) : B) ^ n = 0)
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
      (J : Ideal B'') (k : ℕ), J ^ (k + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') E₀.f, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ φ₀ ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval k (T.toSeries i) s)).1) :
    ∃ (Ñ : E.A ⟶ E'.A) (hÑ : Ñ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
        mapPt Ñ hÑ (E.L.mul t P Q) = E'.L.mul t (mapPt Ñ hÑ P) (mapPt Ñ hÑ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ Ñ = Ñ ≫ E'.act x) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
        P.1 ≫ g ≫ Ñ = (nsmulPt E₀'.L t (q ^ (n * μ)) (mapPt φ₀ hφ₀ P)).1 ≫ g') ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (k : ℕ), J ^ (k + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ Ñ =
            (θ' B'' (fun i => MvFormalGroup.nilEval k
              (((X'.act (((q : ℕ) : Zp2 q) ^ (n * μ))).comp T.toSeries) i) s)).1) := by sorry
