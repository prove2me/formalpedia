-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/b9459bb3-dd2e-55f2-9513-9f882ed94031
-- title:
--   Pasting pull-backs of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$, and let $\varphi : S \to S'$, $\psi : S' \to S''$, $\chi : S \to S''$ be homomorphisms of commutative rings (all in `Type`) with $\psi \circ \varphi = \chi$. Let $E$, $E'$, $E''$ be objects of the project's structure `FakeEllipticCurve Λ N` over $S$, $S'$, $S''$ respectively, each consisting of a scheme `A` over $\operatorname{Spec}$ of the base, a commutative relative group law `L`, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action satisfying homomorphism, unit, multiplicativity, additivity and trace axioms, and level data $\mathrm{lev} : C \to A$. Assume $g' : E'.A \to E.A$ satisfies the project's predicate `IsPullbackVia φ E E' g'`, i.e. the square formed by $g'$, $E'.f$, $E.f$ and $\operatorname{Spec}\varphi$ is cartesian, $g'$ carries the group law of $E'$ to that of $E$ on $T$-points for every $T$ over $\operatorname{Spec} S'$, satisfies $E'.\mathrm{act}\,x \circ g' = g' \circ E.\mathrm{act}\,x$ for all $x \in \Lambda$, and sends sections factoring through $E'.\mathrm{lev}$ to sections whose composite with $g'$ factors through $E.\mathrm{lev}$. Assume in addition the converse level condition `hlev'`: whenever $P$ is a section of $E'.f$ over some $t' : T \to \operatorname{Spec} S'$ and $P \circ g'$ factors through $E.\mathrm{lev}$, then $P$ factors through $E'.\mathrm{lev}$. Finally assume $g : E''.A \to E.A$ satisfies `IsPullbackVia χ E E'' g`. Then there is $g'' : E''.A \to E'.A$ with $g'' \circ g' = g$ and $g'' \circ E'.f = E''.f \circ \operatorname{Spec}\psi$, which is the unique morphism with these two properties, and which satisfies `IsPullbackVia ψ E' E'' g''`.
--
--   This is the two-out-of-three property of cartesian squares, transported to the moduli data of fake elliptic curves with $\Lambda$-action and level structure: a pull-back along a composite factors uniquely through a pull-back along the first map, and the factorisation is itself such a pull-back. It is used in the construction of pull-back and descent data for these moduli, for instance in the uniqueness statements for morphisms representing isogeny pairs and extra level structures, and in the covering argument producing connected charts with a formal module structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'') (χ : S →+* S'') (hχ : ψ.comp φ = χ)
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (E'' : FakeEllipticCurve Λ N S'')

    (g' : E'.A ⟶ E.A) (h' : IsPullbackVia φ E E' g')
    (hlev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g') → FactorsThrough E'.lev P)

    (g : E''.A ⟶ E.A) (h : IsPullbackVia χ E E'' g) :
    ∃ g'' : E''.A ⟶ E'.A, g'' ≫ g' = g ∧ g'' ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) ∧
      (∀ k : E''.A ⟶ E'.A, k ≫ g' = g → k ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) → k = g'') ∧
      IsPullbackVia ψ E' E'' g'' := by sorry
