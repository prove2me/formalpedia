-- Prove2me | Theorems.Thm_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
-- name    : CoherentBaseChange.TwoTermComplex.natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/39016df8-a0f8-5f64-97f5-68fab0720a58
-- title:
--   Euler characteristic of a two-term complex at a field-valued point
-- statement:
--   Let $R$ be a commutative ring and let $G$ be a `TwoTermComplex` over $R$: a pair of $R$-modules $C^0$, $C^1$, each finite and free over $R$, together with an $R$-linear map $d \colon C^0 \to C^1$; its invariant $\chi$ is by definition the integer $\operatorname{rk}_R C^0 - \operatorname{rk}_R C^1$, i.e. the difference of the $R$-finranks of $C^0$ and $C^1$. Let $K$ be a field equipped with an $R$-algebra structure, that is, an arbitrary field-valued point of $\operatorname{Spec} R$ (no finiteness or flatness hypothesis on $R \to K$). Consider the base-changed $K$-linear map $d \otimes K \colon K \otimes_R C^0 \to K \otimes_R C^1$. The assertion is the equality of integers
--   $$\dim_K \ker(d \otimes K) - \dim_K \bigl((K \otimes_R C^1)/\operatorname{im}(d \otimes K)\bigr) = \chi(G),$$
--   the two $K$-dimensions being `Module.finrank`s cast to $\mathbb{Z}$; so the kernel dimension minus the cokernel dimension of $d \otimes K$ is independent of the field-valued point and equals $\operatorname{rk}_R C^0 - \operatorname{rk}_R C^1$.
--
--   This is the constancy of the Euler characteristic of a finite free two-term complex along field-valued points, in the form needed to compare $h^0$ and $h^1$ at geometric points without first passing to residue fields. It is used in the construction of the genus of a smooth proper curve, in the results producing a genus satisfying Riemann–Roch on every geometric fibre, both for the finite-map presentation and for the two-affine-open-cover presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct
open CoherentBaseChange

theorem CoherentBaseChange.TwoTermComplex.natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by sorry
