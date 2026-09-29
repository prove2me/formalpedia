-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_lift_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/25b06be2-5839-50f4-97c0-a6953a59ad49
-- title:
--   Unique lifting of full level-m structures along nilpotent thickenings
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$ and $m$, and commutative rings $S$ and $S_0$ with $S_0$ an $S$-algebra such that the structure map $S \to S_0$ is surjective with nilpotent kernel ideal, and such that the image of $m$ in $S$ is a unit. Let $E$ be a fake elliptic curve over $S$ and $E_0$ one over $S_0$ (for the same $\Lambda$ and $N$), and let $g : E_0.A \to E.A$ be a morphism making the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}$ of $S \to S_0$ cartesian, so that $E_0.A$ is the base change of $E.A$; assume moreover that $g$ is compatible with the relative group laws, in the sense that for every scheme $T$, every $t' : T \to \operatorname{Spec} S_0$ and all $T$-points $P,Q$ of $E_0.A$ over $t'$ one has $(E_0.L.\mathrm{mul}\,t'\,P\,Q)$ followed by $g$ equal to the product, under $E.L$, of $P$ followed by $g$ and $Q$ followed by $g$ over the composite of $t'$ with $\operatorname{Spec}(S \to S_0)$, and that $g$ intertwines the $\Lambda$-actions: $E_0.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$. Let $P_0$ be a full level-$m$ structure on $E_0$, that is, a section of $E_0.f$ over $\operatorname{Spec} S_0$ which is killed by $m$ for the group law $E_0.L$, whose geometric specialisations generate the $m$-torsion under the $\Lambda$-action, and whose annihilator in $\Lambda$ at every geometric point is exactly $m\Lambda$. The conclusion is that there is a unique full level-$m$ structure $P$ on $E$ (a section of $E.f$ over $\operatorname{Spec} S$ with the corresponding $m$-torsion, generation and annihilator conditions at all algebraically closed residue fields of $S$) whose reduction is $P_0$, i.e. with $P_0$ followed by $g$ equal to $\operatorname{Spec}(S \to S_0)$ followed by $P$.
--
--   This is the infinitesimal lifting property for full level-$m$ structures: when $m$ is invertible the $m$-torsion of a fake elliptic curve is finite étale over the base, so its sections lift uniquely across a surjection with nilpotent kernel, and the generation and annihilator conditions are unaffected because geometric points of $S$ factor through $S_0$. It is used in the comparison of level structures under norm transport and in the rigidification step producing transported full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_lift_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    (S S₀ : Type) [CommRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (hm : IsUnit ((m : ℕ) : S))
    (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom (algebraMap S S₀))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (P₀ : E₀.FullLevel m) :
    ∃! P : E.FullLevel m, (P₀.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S₀)) ≫ (P.P).1 := by sorry
