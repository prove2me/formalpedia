-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lift_of_isFormalModuleVia_of_bareDeformation
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_lift_of_isFormalModuleVia_of_bareDeformation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/18f06e9e-3eac-5bf0-8fe4-2f4cd789f3c4
-- title:
--   Upgrading a bare deformation to a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a subgroup $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ (a $\mathbb{Z}$-submodule), a natural number $N$ and a prime $q$, together with a map $\mathrm{coord} : \Lambda \to \mathbb{W}(\mathbb{F}_{q^2})^2$ satisfying `IsOrderCoord`: it is additive and injective, sends $1$ to $(1,0)$, is multiplicative in the twisted sense $\mathrm{coord}(mm') = (\alpha\alpha' + q\beta\,\varphi(\beta'),\ \alpha\beta' + \beta\,\varphi(\alpha'))$ with $\varphi$ the Witt-vector Frobenius, has $q$-adically dense image, and matches reduced traces with $\alpha + \varphi(\alpha)$; assume $1 \in \Lambda$. Let $B$ be an Artinian local ring with algebraically closed residue field and $B_0$ a $B$-algebra with $\mathrm{algebraMap}$ surjective and nilpotent kernel, $q$ nilpotent in $B$ and $N$ a unit in $B$. Given a fake elliptic curve $E_0$ over $B_0$ (an abelian scheme of relative fibre dimension $2$ with commutative relative group law, an action of $\Lambda$ by group-law endomorphisms normalised at $1$, multiplicative and additive in $m$, with the trace condition on tangent spaces, plus a level-$N$ structure), a formal $\mathcal{O}_D$-module $X$ of dimension $2$ over $B$ (a commutative formal group $X.F$ with $\mathbb{W}(\mathbb{F}_{q^2})$-action and a uniformiser series $\varpi$ with $\varpi\circ\varpi = [q]$ and $\varpi\circ[a] = [\varphi(a)]\circ\varpi$), and formal coordinates $\theta_0$ along the unit section of $E_0$ such that $E_0$ is a formal $X \otimes_B B_0$-module via $\mathrm{coord}$ (i.e. $\theta_0$ are formal coordinates for the group law $(X.F)_{B_0}$ and the $\Lambda$-action is computed on coordinates by $[\alpha_m] +_{X.F} [\beta_m]\circ\varpi$), and given a bare deformation $D$ of $(E_0.f, E_0.L)$ to $B$ — an abelian scheme over $B$ with commutative group law together with a cartesian map $D.g$ from $E_0$ compatible with multiplication — and formal coordinates $\theta$ for $X.F$ on $D$ lifting $\theta_0$ through $D.g$ on nilpotent tuples: then there exist a fake elliptic curve $E$ over $B$, a morphism $g : E_0.A \to E.A$ and formal coordinates $\theta'$ on $E$ such that $E_0$ is the pull-back of $E$ along $B \to B_0$ via $g$ (cartesian square, $g$ compatible with the group laws, equivariant for the $\Lambda$-actions, and level structures matching), $E$ is a formal $X$-module via $\mathrm{coord}$ and $\theta'$, and $\theta_0(s)$ followed by $g$ equals $\theta'(s)$ for every nilpotent tuple $s$ over any $B$- and $B_0$-algebra forming a scalar tower.
--
--   This is the final assembly step of Serre–Tate-type lifting for fake elliptic curves at Artinian local points: it converts a bare lift of the underlying abelian scheme, together with formal coordinates realising the prescribed formal $\mathcal{O}_D$-module, into a genuine lift of the quaternionic moduli datum. It is used in the statement of Serre–Tate existence over Artinian local rings with algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lift_of_isFormalModuleVia_of_bareDeformation.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_lift_of_isFormalModuleVia_of_bareDeformation
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B)) (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (X : FormalODModule q B) (θ₀ : RelativeGroupLaw.FormalCoordinates E₀.f 2)
    (h₀ : E₀.IsFormalModuleVia coord (X.map (algebraMap B B₀)) θ₀)
    (D : BareDeformation E₀.f E₀.L B) (θ : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates X.F θ) (hlift : D.LiftsCoordinates θ₀ θ) :
    ∃ (E : FakeEllipticCurve Λ N B) (g : E₀.A ⟶ E.A) (θ : RelativeGroupLaw.FormalCoordinates E.f 2),
      FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E E₀ g ∧
      E.IsFormalModuleVia coord X θ ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B''] (s : Fin 2 → B''),
        (∀ i, IsNilpotent (s i)) → (θ₀ B'' s).1 ≫ g = (θ B'' s).1 := by sorry
