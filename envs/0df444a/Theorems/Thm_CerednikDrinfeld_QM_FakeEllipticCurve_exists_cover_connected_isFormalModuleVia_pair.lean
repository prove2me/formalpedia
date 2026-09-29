-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isFormalModuleVia_pair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isFormalModuleVia_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/95c1c46d-16b8-5ad1-984a-50d9d2334826
-- title:
--   Common connected formal-coordinate cover for two fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a prime $q$, and a map $\mathrm{coord}\colon \Lambda \to \mathbb{Z}_{q^2}\times\mathbb{Z}_{q^2}$ (values in $\mathrm{Zp2}\,q$, the Witt vectors of the field with $q^2$ elements) satisfying `IsOrderCoord`: additivity, $1 \mapsto (1,0)$, the twisted multiplication rule involving $q$ and the Witt-vector Frobenius, injectivity, $q$-adic density of the image, and the trace condition $(\mathrm{coord}\,m)_1 + \varphi((\mathrm{coord}\,m)_1) = n$ whenever $m + \bar m = n$. Let $B$ be a Noetherian commutative ring in which $q$ is nilpotent, and let $E, E'$ be two fake elliptic curves over $B$ in the sense of `FakeEllipticCurve Λ N B`. Then there are $n \in \mathbb{N}$ and $f \colon \mathrm{Fin}\,n \to B$ whose range generates the unit ideal of $B$ such that for every index $i$ and every commutative $B$-algebra $L$ which is a localisation of $B$ away from $f_i$ (any model, not just `Localization.Away`): every idempotent of $L$ is $0$ or $1$; and for each of $E$ and $E'$ separately, every fake elliptic curve $E_1$ over $L$ together with a morphism to the corresponding total space exhibiting it as a pullback along $B \to L$ in the sense of `IsPullbackVia` (a pullback square of schemes, compatibility with the relative group law and with the $\Lambda$-action, and descent of level points) admits a formal $\mathcal{O}_D$-module $X$ over $L$ — a commutative two-dimensional formal group law with $\mathbb{Z}_{q^2}$-action by power series and a uniformiser $\varpi$ with $\varpi\circ\varpi = [q]$ and $\varpi \circ [\alpha] = [\varphi(\alpha)]\circ\varpi$ — and formal coordinates $\theta$ in two variables for the structure morphism of $E_1$, such that $\theta$ is a system of formal coordinates for the relative group law with formal group $X.F$ and the action of each $m \in \Lambda$ on infinitesimal points is computed by the power series $X.F$-sum of $[(\mathrm{coord}\,m)_1]$ and $[(\mathrm{coord}\,m)_2]\circ\varpi$.
--
--   This is the two-curve, any-model form of the statement that the formal $\mathcal{O}_D$-module structure on the formal group of a fake elliptic curve in characteristic dividing $q$ exists after a finite Zariski localisation with connected spectrum; it packages the special formal module datum of Čerednik–Drinfeld theory in the shape required downstream. It is used to produce simultaneous local formal coordinates for a curve and an auxiliary curve, for instance in the rigidification and Atkin–Lehner comparison arguments of the uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isFormalModuleVia_pair.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isFormalModuleVia_pair
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] [IsNoetherianRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E E' : FakeEllipticCurve Λ N B) :
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L],
        (∀ e : L, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (∀ (E₁ : FakeEllipticCurve Λ N L) (g : E₁.A ⟶ E.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B L) E E₁ g →
            ∃ (X : FormalODModule q L) (θ : RelativeGroupLaw.FormalCoordinates E₁.f 2), E₁.IsFormalModuleVia coord X θ) ∧
        (∀ (E₁' : FakeEllipticCurve Λ N L) (g' : E₁'.A ⟶ E'.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B L) E' E₁' g' →
            ∃ (X' : FormalODModule q L) (θ' : RelativeGroupLaw.FormalCoordinates E₁'.f 2), E₁'.IsFormalModuleVia coord X' θ') := by sorry
