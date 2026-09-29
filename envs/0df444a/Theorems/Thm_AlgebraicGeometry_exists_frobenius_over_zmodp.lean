-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_frobenius_over_zmodp
-- name    : AlgebraicGeometry.exists_frobenius_over_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0d0e5bb1-0ec2-5379-8646-83c12ef5974f
-- title:
--   Absolute Frobenius endomorphism of a scheme over 𝔽ₚ
-- statement:
--   Let $p$ be a prime number and let $X$ be a scheme whose underlying data live in the lowest universe, equipped with a morphism $f : X \to \operatorname{Spec}(\mathbb{Z}/p)$, where $\mathbb{Z}/p$ is viewed as a commutative ring object. The assertion is that there exists an endomorphism $F : X \to X$ with two properties. First, $F$ followed by $f$ equals $f$, so $F$ is an endomorphism of $X$ over the base $\operatorname{Spec}(\mathbb{Z}/p)$. Second, $F$ is pinned down on affine points in the following sense: for every commutative ring $B$ in the lowest universe which is a $\mathbb{Z}/p$-algebra and has characteristic $p$ (as recorded by `CharP B p`), and for every morphism $x : \operatorname{Spec}(B) \to X$ such that $x$ followed by $f$ is the morphism $\operatorname{Spec}$ of the structure map $\mathbb{Z}/p \to B$ — that is, $x$ is a $\operatorname{Spec}(\mathbb{Z}/p)$-point of $X$ with values in $B$ — one has the equality $\operatorname{Spec}(\mathrm{frob}_{B,p})$ followed by $x$ equals $x$ followed by $F$, where $\mathrm{frob}_{B,p} : B \to B$ is the ring endomorphism $b \mapsto b^{p}$. No uniqueness of $F$ is asserted.
--
--   This is the absolute Frobenius endomorphism of a scheme of characteristic $p$, presented as a morphism of schemes over $\operatorname{Spec}(\mathbb{F}_p)$ together with its compatibility with the ring-theoretic Frobenius on affine points, which is the form in which it is used. It supplies the Frobenius endomorphism as data for the special-fibre arguments on modular curves and their Néron models, in particular for the statement relating Verschiebung composed with Frobenius to multiplication by $p$, and for the descent and idempotent-splitting statements about Raynaud quotients at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_frobenius_over_zmodp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_frobenius_over_zmodp
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) :
    ∃ F : X ⟶ X, F ≫ f = f ∧
      ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F := by sorry
