-- Prove2me | Theorems.Thm_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
-- name    : Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/dc11fe54-7acf-5ed8-9589-6f43947c2012
-- title:
--   Locally constant ℤ/p-valued Amitsur cocycles over ℤ are coboundaries
-- statement:
--   Let $p$ be a nonzero natural number and let $A$ be a commutative ring which is faithfully flat as a $\mathbb{Z}$-module. Let $c$ be a locally constant $\mathbb{Z}/p$-valued function on the prime spectrum of the two-fold Amitsur term `R₂ ℤ A` (the tensor product $A\otimes_{\mathbb{Z}}A$), and assume the additive cocycle identity: the pullbacks of $c$ along the spectrum maps induced by the coface homomorphisms `c₁₂ ℤ A` and `c₂₃ ℤ A` add up to its pullback along the one induced by `c₁₃ ℤ A`. The conclusion asserts the existence of a type $B$ carrying a commutative ring structure which is nontrivial, finite and flat as a $\mathbb{Z}$-module and formally unramified over $\mathbb{Z}$, together with an $A$-algebra isomorphism $A\otimes_{\mathbb{Z}}B\cong(\mathbb{Z}/p\to A)$, such that $B$ admits a ring homomorphism to $\mathbb{Z}$ if and only if $c$ is a coboundary, i.e. there is a locally constant $\mathbb{Z}/p$-valued function $b$ on $\operatorname{Spec}A$ with $c$ equal to the difference of the pullbacks of $b$ along the spectrum maps induced by `i₁ ℤ A` and `i₂ ℤ A`. Since the statement is existential in $B$, it does not pin down a particular twisted form.
--
--   This is the vanishing of the degree-one Amitsur (Čech) cohomology of the constant sheaf $\mathbb{Z}/p$ for a faithfully flat $\mathbb{Z}$-algebra $A$, packaged together with the twisted form of the split algebra $\mathbb{Z}^{\mathbb{Z}/p}$ attached to such a cocycle. It is used in the proof that the constant $\mathbb{Z}/p$ sheaf is Amitsur-trivial for the fppf topology, via [`AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf`](thm.html#AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary.lean

import Mathlib
import Definitions.Def_Algebra_DescentCofaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Algebra.DescentCofaces AlgebraicGeometry
open scoped TensorProduct

theorem Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
    (p : ℕ) (hp : p ≠ 0) (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A]
    (c : LocallyConstant (PrimeSpectrum (R₂ ℤ A)) (ZMod p))
    (hc : c.comap (Spec.topMap (c₁₂ ℤ A)).hom + c.comap (Spec.topMap (c₂₃ ℤ A)).hom =
        c.comap (Spec.topMap (c₁₃ ℤ A)).hom) :
    ∃ (B : Type) (_ : CommRing B) (_ : Nontrivial B) (_ : Module.Finite ℤ B) (_ : Module.Flat ℤ B)
      (_ : Algebra.FormallyUnramified ℤ B) (_ : A ⊗[ℤ] B ≃ₐ[A] (ZMod p → A)),
      Nonempty (B →+* ℤ) ↔
        ∃ b : LocallyConstant (PrimeSpectrum A) (ZMod p),
          c = b.comap (Spec.topMap (i₁ ℤ A)).hom - b.comap (Spec.topMap (i₂ ℤ A)).hom := by sorry
