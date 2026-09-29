-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/4eae6325-ad05-5b20-9514-3288e695b3d6
-- title:
--   Unique lifting of full level-m structures along nilpotent thickenings
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N,m\in\mathbb{N}$, let $S$ be a local commutative ring and $S_0$ a commutative ring, and let $E$ and $E_0$ be fake elliptic curves with $\Lambda$-action and level-$N$ data (in the sense of the project's structure `FakeEllipticCurve`) over $S$ and over $S_0$ respectively. Assume the image of $m$ in $S$ is a unit, and let $p\colon S\to S_0$ be a surjective ring homomorphism whose kernel is a nilpotent ideal. Let $g\colon E_0.A\to E.A$ be a morphism making the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}(p)$ cartesian, compatible with the relative group laws in the sense that for every scheme $T$, every $t'\colon T\to\operatorname{Spec}S_0$ and all $T$-points $P,Q$ of $E_0.f$ over $t'$ the composite of $E_0.L.\mathrm{mul}\,t'\,P\,Q$ with $g$ is the product in $E.L$ over $t'$ followed by $\operatorname{Spec}(p)$ of the two points $P\circ g$, $Q\circ g$, and compatible with the actions, $E_0.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $E.\mathrm{act}(x)$ for all $x\in\Lambda$. Let $P_0$ be a full level-$m$ structure on $E_0$, i.e. a section of $E_0.f$ over $\operatorname{Spec}S_0$ which is killed by $m$ for the group law, which at every geometric point ($k$ algebraically closed, $s_k\colon S_0\to k$) has its $\Lambda$-orbit equal to the whole $m$-torsion, and whose annihilator there is exactly $m\Lambda$. Then there is exactly one full level-$m$ structure $P$ on $E$ whose underlying section satisfies $P_0 \text{ followed by } g = \operatorname{Spec}(p)$ followed by $P$.
--
--   This is the infinitesimal lifting (deformation) property of full level structures of order invertible on the base, in the style of the corresponding statement for elliptic curves in Katz–Mazur: along a nilpotent thickening of the base, passage to the reduction is a bijection on full level-$m$ structures. It is used in the construction of the fine moduli problem for fake elliptic curves with full level structure, in particular in the results asserting the existence and uniqueness of pullbacks of objects `WithFullLevel` along small and Artinian extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [IsLocalRing S] [CommRing S₀]
    (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (P₀ : E₀.FullLevel m) :
    ∃! P : E.FullLevel m, (P₀.P).1 ≫ g = Spec.map (CommRingCat.ofHom p) ≫ (P.P).1 := by sorry
