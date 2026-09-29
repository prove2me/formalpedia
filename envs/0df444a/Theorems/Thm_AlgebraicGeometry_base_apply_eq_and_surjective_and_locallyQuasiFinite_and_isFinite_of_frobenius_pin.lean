-- Prove2me | Theorems.Thm_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin
-- name    : AlgebraicGeometry.base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/17d2eac4-865f-5107-8e98-68660a7b2656
-- title:
--   Frobenius pinned by B-points is finite and topologically trivial
-- statement:
--   Let $p$ be a prime, let $X$ be a scheme (in the bottom universe) and let $f \colon X \to \operatorname{Spec}(\mathbb{Z}/p)$ be a morphism that is locally of finite type. Let $F \colon X \to X$ be an endomorphism with $F$ followed by $f$ equal to $f$, and suppose $F$ is pinned by Frobenius on points in the following sense: for every commutative ring $B$ carrying a $\mathbb{Z}/p$-algebra structure and satisfying $\operatorname{char} B = p$, and every morphism $x \colon \operatorname{Spec} B \to X$ such that $x$ followed by $f$ is the morphism induced by the structure map $\mathbb{Z}/p \to B$, the composite $\operatorname{Spec}(\mathrm{frob}_{B,p})$ followed by $x$ equals $x$ followed by $F$, where $\mathrm{frob}_{B,p}$ is the $p$-power ring endomorphism of $B$. The conclusion is a sixfold conjunction: $F$ induces the identity on the underlying topological space, i.e. $F.\mathrm{base}\,x = x$ for every point $x$ of $X$; and $F$ is surjective, quasi-compact, locally quasi-finite, affine and finite.
--
--   This is the standard description of the absolute Frobenius endomorphism of a scheme locally of finite type over $\mathbb{F}_p$: it is the identity on the underlying space and is a finite morphism, the finiteness resting on the finite-type hypothesis (the $p$-th power map on $\mathbb{F}_p(t_1,t_2,\dots)$ is not module-finite). It is used in the construction of the Verschiebung factorisation of multiplication by $n$ for the modular-curve object at $p$, in [`ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul`](thm.html#ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) [LocallyOfFiniteType f]
    (F : X ⟶ X) (hFb : F ≫ f = f)
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F) :
    (∀ x : X, F.base x = x) ∧ Surjective F ∧ QuasiCompact F ∧ LocallyQuasiFinite F ∧ IsAffineHom F ∧ IsFinite F := by sorry
