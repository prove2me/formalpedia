-- Prove2me | Theorems.Thm_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul
-- name    : CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/805ab338-fa73-5add-9b78-f772247672f6
-- title:
--   Künneth dimension formula over a field for bounded cochain complexes
-- statement:
--   Let $k$ be a field and let $C$ and $D$ be bounded $\mathbb{N}$-indexed cochain complexes of $k$-vector spaces in the project's sense: each consists of modules $C^p$ for $p \in \mathbb{N}$, $k$-linear differentials $d^p \colon C^p \to C^{p+1}$ with $d^{p+1} \circ d^p = 0$, together with a bound $N$ such that $C^n$ is a subsingleton for all $n \ge N$. Assume that for every $p$ the cohomology space `C.H p` is a finite $k$-module, and likewise `D.H q` for every $q$, and let $n \in \mathbb{N}$. Form `C.tensor D`, the bounded double complex with entries $C^p \otimes_k D^q$, horizontal differential $d^p_C \otimes \mathrm{id}$, vertical differential $\mathrm{id} \otimes d^q_D$, and bound $\max(N_C, N_D)$, and let [`DoubleComplex.HTot`](def/AlgebraicGeometry_DoubleComplex.html#L65) denote its total cohomology in degree $n$, namely the quotient of $\ker$ of the total differential $d_{\mathrm{Tot}}^n$ (assembled from the horizontal and vertical parts with the sign $(-1)^p$) by the submodule of those cocycles lying in the image of $d_{\mathrm{Tot}}^{n-1}$, this submodule being $\bot$ when $n = 0$. The conclusion is that this total cohomology space is a finite $k$-module and that $$\dim_k H^n(\mathrm{Tot}(C \otimes_k D)) = \sum_{i=0}^{n} \dim_k \mathrm{C.H}\, i \cdot \dim_k \mathrm{D.H}\, (n-i),$$ the indices $n - i$ being truncated subtraction in $\mathbb{N}$.
--
--   This is the Künneth formula over a field in its dimension form, for the total complex of the tensor product double complex of two bounded complexes with finite-dimensional cohomology. It is used in the Čech-theoretic dimension count [`AlgebraicGeometry.OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul
    {k : Type u} [Field k] (C D : CochainCx.Bounded k)
    (hC : ∀ p, Module.Finite k (C.H p)) (hD : ∀ q, Module.Finite k (D.H q)) (n : ℕ) :
    Module.Finite k (DoubleComplex.HTot (C.tensor D) n) ∧
      Module.finrank k (DoubleComplex.HTot (C.tensor D) n) =
        ∑ i ∈ Finset.range (n + 1), C.hfinrank i * D.hfinrank (n - i) := by sorry
