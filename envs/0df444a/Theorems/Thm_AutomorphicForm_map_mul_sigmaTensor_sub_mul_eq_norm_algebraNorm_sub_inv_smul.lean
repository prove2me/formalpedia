-- Prove2me | Theorems.Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
-- name    : AutomorphicForm.map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/af16b6c9-a0a2-5e36-9a56-69dc644966c1
-- title:
--   Module of x ↦ a σ(x) - bx on L ⊗_K Kᵥ
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ that is Galois over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and assume every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$, so that $\mathrm{Gal}(L/K)$ is cyclic with generator $\sigma$. Let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and write $K_v$ for the $v$-adic completion of $K$. Equip the $K_v$-algebra $E = L \otimes_K K_v$ with a measurable structure that is the Borel structure of its topology, and let $\nu$ be an additive Haar measure on $E$. Let $a, b \in E$ satisfy $N(a) \neq N(b)$, where $N$ denotes the algebra norm $E \to K_v$ (the determinant of multiplication). Then the pushforward of $\nu$ along the map $x \mapsto a\,(\sigma \otimes \mathrm{id}_{K_v})(x) - b\,x$, where $\sigma \otimes \mathrm{id}_{K_v}$ is the ring endomorphism [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199) of $E$ induced by $\sigma$ on the left factor, equals $\|N(a) - N(b)\|^{-1} \cdot \nu$, the scaling factor being the inverse $v$-adic absolute value of $N(a) - N(b)$, viewed as an element of $[0, \infty]$.
--
--   This is the computation of the module (Jacobian) of the twisted difference operator $x \mapsto a\,\sigma(x) - bx$ on the semilocal algebra $L \otimes_K K_v = \prod_{w \mid v} L_w$, in the form used by Langlands in the base-change comparison of twisted orbital integrals; the underlying linear algebra gives $\det_{K_v} = \pm(N(a) - N(b))$ for any degree and any behaviour of $v$ in $L$. The case $a = 1$ is extracted in [`AutomorphicForm.map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul`](thm.html#AutomorphicForm.map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (a b : L ⊗[K] v.adicCompletion K)
    (hab : Algebra.norm (v.adicCompletion K) a ≠ Algebra.norm (v.adicCompletion K) b) :
    Measure.map (fun x : L ⊗[K] v.adicCompletion K =>
        a * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x - b * x) ν =
      ENNReal.ofReal
          ‖Algebra.norm (v.adicCompletion K) a - Algebra.norm (v.adicCompletion K) b‖⁻¹ • ν := by sorry
