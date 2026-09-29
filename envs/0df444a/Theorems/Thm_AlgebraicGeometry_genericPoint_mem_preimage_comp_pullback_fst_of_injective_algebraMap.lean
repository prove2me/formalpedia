-- Prove2me | Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
-- name    : AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/bed3f0bb-11cd-5ba6-9aef-65dadb294f33
-- title:
--   Generic point of an integral generic-fibre model meets every nonempty open
-- statement:
--   Let $R$ be a commutative ring, $K$ a field and $R \to K$ an $R$-algebra structure whose structure map $\mathrm{algebraMap}\ R\ K$ is injective, and write $\iota = \operatorname{Spec}$ of that homomorphism, a morphism $\operatorname{Spec} K \to \operatorname{Spec} R$. Let $X$ be a scheme which is integral (in the Mathlib sense: nonempty and with reduced, irreducible underlying space), let $c \colon X \to \operatorname{Spec} R$ be a morphism of schemes, and let $Y$ be a further integral scheme equipped with a morphism $e_0 \colon Y \to \operatorname{pullback}(c, \iota)$ which is an isomorphism; thus $Y$ is an integral model of the base change $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$. Finally let $U$ be an open subscheme of $X$ whose underlying set is nonempty. The conclusion is that the generic point $\eta_Y$ of $Y$ lies in the open subset of $Y$ obtained by pulling back $U$ along the composite $g = e_0$ followed by the first projection $\operatorname{pullback.fst}(c,\iota) \colon \operatorname{pullback}(c,\iota) \to X$; equivalently $g(\eta_Y) \in U$ for every nonempty open $U \subseteq X$.
--
--   This is the elementary statement that, when $R$ embeds in a field $K$, the composite $Y \cong X \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X$ sends the generic point of $Y$ to the generic point of $X$, so that it lands in every nonempty open of $X$. It is used when comparing the function field of an integral scheme over $R$ with that of its generic fibre, in particular in the identification of function fields of curve models via pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsIntegral X]
    {Y : Scheme.{u}} [IsIntegral Y]
    (e₀ : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint Y ∈ (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ U := by sorry
