-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/2a804f6d-18e9-5923-bdfe-c8e31fd1e304
-- title:
--   Extra levels lift along nilpotent thickenings
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and commutative rings $S$, $S_0$. Let $E$ be a fake elliptic curve over $S$ and $E_0$ one over $S_0$, both for the data $(\Lambda, N)$, and let $\ell$ be a natural number that is a unit in $S$. Let $p : S \to S_0$ be a surjective ring homomorphism whose kernel is a nilpotent ideal, and let $g : E_0.A \to E.A$ be a morphism such that the square formed by $g$, the structure morphisms $E_0.f$, $E.f$ and $\operatorname{Spec}(p)$ is cartesian, and such that: (i) for every scheme $T$, every $t' : T \to \operatorname{Spec} S_0$ and all $T$-points $P,Q$ of $E_0.A$ over $t'$, composing the product $E_0.L.\mathrm{mul}\,t'\,P\,Q$ with $g$ gives the product of $P \circ g$ and $Q \circ g$ for the group law of $E$ over $t'$ followed by $\operatorname{Spec}(p)$; (ii) for each $x \in \Lambda$, $E_0.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$; (iii) every point of $E_0$ factoring through $E_0.\mathrm{lev}$ has its image under $g$ factoring through $E.\mathrm{lev}$. These are the clauses of the pullback predicate for $p$, with the witness $g$ named. Then for every extra level $K_0$ at $\ell$ on $E_0$ — a closed immersion $K_0.\mathrm{levK}$ into $E_0.A$ whose points are closed under the group law and inversion, contain the unit, are killed by $\ell$, are stable under the $\Lambda$-action and meet the points of $E_0.\mathrm{lev}$ only in the unit, with $K_0.\mathrm{levK}$ followed by $E_0.f$ finite, flat and locally of finite presentation of rank $\ell^2$ at every point of $\operatorname{Spec} S_0$, and with geometric fibre group isomorphic to $(\mathbb{Z}/\ell)^2$ wherever $\ell \neq 0$ — there exists an extra level $K$ at $\ell$ on $E$ such that for every $T$, every $t' : T \to \operatorname{Spec} S_0$ and every $T$-point $P$ of $E_0.A$ over $t'$ factoring through $K_0.\mathrm{levK}$, the composite $P \circ g$ factors through $K.\mathrm{levK}$. The conclusion asserts only this one inclusion of points, not that $K$ base-changes back to $K_0$.
--
--   This is the deformation-theoretic step that an $\ell$-level structure (an extra level subgroup of order $\ell^2$) on a fake elliptic curve over a quotient by a nilpotent ideal extends to the curve itself, $\ell$ being invertible, so that extra levels are unobstructed along nilpotent thickenings. It is used in the construction of rigidifications and of Frobenius twists of fake elliptic curves carrying extra level structure in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (hlev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' E₀.f),
      FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g)
    (K₀ : E₀.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough K₀.levK P → ∃ P₀ : T ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ g := by sorry
