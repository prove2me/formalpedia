-- Prove2me | Theorems.Thm_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv
-- name    : CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1275ddfe-fb8b-5b85-bbd6-8d23463e158c
-- title:
--   Unimodularity of a generator of ker d under universal freeness of H⁰
-- statement:
--   Let $R$ be a commutative ring and let $G$ be a two-term complex over $R$ in the sense of the project's structure [`CoherentBaseChange.TwoTermComplex`](def/AlgebraicGeometry_CoherentBaseChange.html#L19): a pair of $R$-modules $C^0 =$ `G.C0` and $C^1 =$ `G.C1`, each finite and free over $R$, together with an $R$-linear map $d =$ `G.d` $: C^0 \to C^1$ (here $C^0$, $C^1$ and the test algebras all live in one and the same universe). Let $g_0 \in C^0$. Assume: (i) every $x \in C^0$ with $d(x) = 0$ is of the form $r \cdot g_0$ for some $r \in R$, i.e. $\ker d \subseteq R g_0$; and (ii) for every commutative $R$-algebra $C$ the $C$-module `G.H0 C` — the submodule of $C \otimes_R C^0$ cut out by the base change of $d$ to $C$ — admits a $C$-linear isomorphism onto $C$, the hypothesis being a `Nonempty` assertion about such isomorphisms for all $C$ simultaneously. Then for every nontrivial commutative $R$-algebra $C$ the element $1 \otimes g_0$ of $C \otimes_R C^0$ is non-zero. Note that $d(g_0) = 0$ is not assumed.
--
--   This is the commutative-algebra content of cohomology and base change in degree $0$ for a family whose direct image is universally an invertible module: if the kernel of the base-changed differential is free of rank one over every $R$-algebra, then a generator of $\ker d$ is unimodular, so its image in $C \otimes_R C^0$ survives for every nontrivial $C$, in particular over every residue field of $R$. It is used in the scheme-theoretic statement [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv), a step towards trivialising an invertible module near a fibre on which it is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (g₀ : G.C0)
    (hker : ∀ x : G.C0, G.d x = 0 → ∃ r : R, x = r • g₀)
    (hH0 : ∀ (C : Type u) [CommRing C] [Algebra R C], Nonempty (G.H0 C ≃ₗ[C] C))
    (C : Type u) [CommRing C] [Algebra R C] [Nontrivial C] :
    ((1 : C) ⊗ₜ[R] g₀ : C ⊗[R] G.C0) ≠ 0 := by sorry
