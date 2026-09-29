-- Prove2me | Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2ea0e439-c058-5b30-b44e-d85523db0d45
-- title:
--   Finite component at v of c(z) diag(a,b)
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and let $z,a,b$ be units of the adele ring $\mathbb{A}_K$ of $K$. Form in $GL_2(\mathbb{A}_K)$ the product of the central scalar matrix attached to $z$, namely [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) applied to $z$, which is the image of $z$ under `Matrix.GeneralLinearGroup.scalar (Fin 2)`, with `diagUnits2 a b`, the invertible matrix whose underlying matrix is $!![a,0;0,b]$ and whose inverse is $!![a^{-1},0;0,b^{-1}]$. Apply to this product the group homomorphism `AdelicLevel.glFin`, induced entrywise by the ring homomorphism $\mathbb{A}_K \to \mathbb{A}_{K,\mathrm{fin}}$ sending an adele to its finite component (its second coordinate), and then `AdelicLevel.finComponent` at $v$, induced entrywise by evaluation of a finite adele at $v$, landing in $GL_2(K_v)$ for $K_v$ the $v$-adic completion. The assertion is that the underlying $2\times 2$ matrix over $K_v$ of the resulting element is the diagonal matrix with entries $z_v a_v$ and $z_v b_v$, where for a unit $u$ of $\mathbb{A}_K$ the symbol $u_v$ denotes the value at $v$ of the finite component of the adele underlying $u$.
--
--   This is a bookkeeping identity identifying the local component at a finite place of a product of a central element and a diagonal torus element in the adelic group $GL_2(\mathbb{A}_K)$; it is used repeatedly in the manipulation of automorphic forms on $GL_2$, in particular when computing window sums, orbital integrals and class sums against central characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b)) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal
        ![(((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
            (((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
          (((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
            (((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v] := by sorry
