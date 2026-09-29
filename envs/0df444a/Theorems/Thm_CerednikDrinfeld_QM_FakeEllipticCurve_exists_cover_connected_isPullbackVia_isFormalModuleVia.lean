-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isPullbackVia_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/fc86335d-464b-5e46-a0e8-20ff9311e259
-- title:
--   Formal mathcal O_D-modules over a connected basic-open cover
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, and a prime $q$; let $\mathrm{coord} : \Lambda \to \mathbb Z_{q^2}\times\mathbb Z_{q^2}$ (values in $W(\mathbb F_{q^2})^2$) satisfy `IsOrderCoord`, i.e. it is additive and injective, sends $1$ to $(1,0)$, is multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta') = (\alpha\alpha' + q\,\beta\,\sigma(\beta'),\ \alpha\beta' + \beta\,\sigma(\alpha'))$ with $\sigma$ the Witt-vector Frobenius, has dense image modulo every power of $q$, and satisfies $\alpha + \sigma(\alpha) = n$ whenever $m + \bar m = n$. Let $B$ be a Noetherian commutative ring in which the image of $q$ is nilpotent, and let $E$ be a fake elliptic curve over $B$ (an abelian scheme $E.f : E.A \to \operatorname{Spec} B$ with two-dimensional fibres, a commutative relative group law, a $\Lambda$-action by endomorphisms over $B$ compatible with addition, multiplication and traces, and a level-$N$ section datum). Then there is a finite subset $s \subseteq B$ generating the unit ideal such that for every $c \in s$: first, the localisation $B[c^{-1}]$ has no idempotents other than $0$ and $1$; and second, for every fake elliptic curve $E'$ over $B[c^{-1}]$ and every morphism $g : E'.A \to E.A$ exhibiting $E'$ as a pullback of $E$ along $\operatorname{Spec} B[c^{-1}] \to \operatorname{Spec} B$ in the sense of `IsPullbackVia` (the square is cartesian, $g$ carries the group law of $E'$ to that of $E$, $g$ intertwines the two $\Lambda$-actions, and points factoring through the level structure of $E'$ push forward to points factoring through that of $E$), there exist a formal $\mathcal O_D$-module $X$ over $B[c^{-1}]$ — a commutative two-dimensional formal group with a $\mathbb Z_{q^2}$-action by series and a series $\varpi$ with $\varpi\circ\varpi = [q]$ and $\varpi\circ[\alpha] = [\sigma(\alpha)]\circ\varpi$ — together with formal coordinates $\theta$ of dimension $2$ along the unit section of $E'.f$, such that $\theta$ is a system of formal coordinates for the relative group law of $E'$ with formal group $X.F$ and, for every $m \in \Lambda$, $\theta$ transports the series $[\,(\mathrm{coord}\,m)_1] + [(\mathrm{coord}\,m)_2]\circ\varpi$ to the endomorphism $E'.\mathrm{act}\,m$ on infinitesimal points.
--
--   This is the local trivialisation step of the Čerednik–Drinfeld theory: over a base in which $q$ is nilpotent, the formal completion of a fake elliptic curve along its unit section is a formal $\mathcal O_D$-module, here obtained on a finite cover of $\operatorname{Spec} B$ by basic opens whose rings are connected (no nontrivial idempotents), and for arbitrary named pullbacks of $E$ to those opens. It refines the corresponding statement without the connectedness requirement, and is used downstream in the rigidification of fake elliptic curves and the comparison of level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isPullbackVia_isFormalModuleVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] [IsNoetherianRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧
      ∀ c ∈ s,
        (∀ e : Localization.Away c, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (∀ (E' : FakeEllipticCurve Λ N (Localization.Away c)) (g : E'.A ⟶ E.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B (Localization.Away c)) E E' g →
            ∃ (X : FormalODModule q (Localization.Away c)) (θ : RelativeGroupLaw.FormalCoordinates E'.f 2),
              E'.IsFormalModuleVia coord X θ) := by sorry
