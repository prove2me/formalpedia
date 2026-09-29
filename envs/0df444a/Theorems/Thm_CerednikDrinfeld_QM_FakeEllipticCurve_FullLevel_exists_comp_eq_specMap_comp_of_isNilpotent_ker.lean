-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/4eaeb4ce-c459-58ab-b6ca-b99201cba52f
-- title:
--   Lifting full level-m structures along nilpotent thickenings
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, and commutative rings $S$, $S_0$. Let $E$ be a fake elliptic curve with $\Lambda$-action and level-$N$ data over $S$ and $E_0$ one over $S_0$, in the sense of the project structure `FakeEllipticCurve`. Let $m$ be a natural number whose image in $S$ is a unit, and let $p : S \to S_0$ be a surjective ring homomorphism whose kernel is a nilpotent ideal. Assume given $g : E_0.A \to E.A$ such that the square formed by $g$, the structure morphisms $E_0.f$ and $E.f$ and $\mathrm{Spec}(p)$ is cartesian; that $g$ is additive on points, i.e. for every scheme $T$, every $t' : T \to \mathrm{Spec}\,S_0$ and all points $P,Q$ of $E_0.A$ over $t'$, the product $E_0.L.\mathrm{mul}\,t'\,P\,Q$ followed by $g$ equals the $E.L$-product of $P$ followed by $g$ and $Q$ followed by $g$, taken over $t'$ followed by $\mathrm{Spec}(p)$; and that $g$ intertwines the actions, $E_0.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$. Then for every full level-$m$ structure $P_0$ on $E_0$ there exists a full level-$m$ structure $P$ on $E$ with $P_0$ followed by $g$ equal to $\mathrm{Spec}(p)$ followed by $P$. Here a full level-$m$ structure on a fake elliptic curve is a section of the structure morphism over the identity that is killed by $m$ for the relative group law, whose $\Lambda$-orbit at each geometric point with algebraically closed residue field exhausts the $m$-torsion, and whose annihilator in $\Lambda$ at each such point is exactly $m\Lambda$. Only existence is asserted, and no compatibility of $g$ with the level-$N$ data is required.
--
--   This is the deformation-theoretic step expressing that the full level-$m$ datum is unobstructed along nilpotent thickenings of the base, $m$ being invertible: level structures descend and lift along a cartesian base change with nilpotent kernel. It is used by the corresponding uniqueness-and-existence statements and by the transport of full level structures across a rigidification of the moduli problem for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
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
    ∃ P : E.FullLevel m, (P₀.P).1 ≫ g = Spec.map (CommRingCat.ofHom p) ≫ (P.P).1 := by sorry
