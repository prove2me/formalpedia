-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field
-- name    : AlgebraicGeometry.Scheme.Hom.ker_pullback_fst_specMap_eq_bot_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/2099979d-0eb7-5272-b005-37dd45e63dfa
-- title:
--   Trivial kernel for base change along Spec of a k₀-algebra
-- statement:
--   Let $k_0$ be a field and let $\bar B$ be a nontrivial commutative ring, and let $\psi : k_0 \to \bar B$ be a ring homomorphism; let $T$ be a scheme and $t : T \to \operatorname{Spec} k_0$ a morphism of schemes. Form the fibre product of $t$ with the morphism $\operatorname{Spec}(\psi) : \operatorname{Spec}\bar B \to \operatorname{Spec} k_0$ induced by $\psi$, and let $\mathrm{pr}_1 : T \times_{\operatorname{Spec} k_0} \operatorname{Spec}\bar B \to T$ be the first projection of that pullback. The assertion is that the kernel ideal sheaf of $\mathrm{pr}_1$ on $T$, in the sense of Mathlib's `Scheme.Hom.ker`, is the zero ideal sheaf $\bot$; equivalently, for every affine open $U \subseteq T$ the comorphism $\mathcal{O}_T(U) \to \mathcal{O}(\mathrm{pr}_1^{-1}U)$ is injective. No reducedness, finiteness or quasi-separatedness hypotheses are imposed on $T$, and $\psi$ is an arbitrary ring homomorphism; nontriviality of $\bar B$ is the only condition on the target ring.
--
--   This is the scheme-theoretic form of the statement that base change of a $k_0$-scheme to a nonzero $k_0$-algebra does not kill functions: the projection remains scheme-theoretically dominant. It is used in the Čerednik–Drinfel'd part of the development, in the verification that a level structure is preserved under a pullback comparison for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.ker_pullback_fst_specMap_eq_bot_of_field
    {k₀ : Type} [Field k₀] {Bb : Type} [CommRing Bb] [Nontrivial Bb] (ψ : k₀ →+* Bb)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) :
    (pullback.fst t (Spec.map (CommRingCat.ofHom ψ))).ker = ⊥ := by sorry
