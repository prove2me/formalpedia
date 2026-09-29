-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
-- name    : AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/098cc988-0734-5de0-ac3b-258aacb1f6ad
-- title:
--   Haar measure on GL₂(L⊗_K Kᵥ) in matrix coordinates
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal O_K$, and write $E = L \otimes_K K_v$ for the tensor product of $L$ with the $v$-adic completion $K_v$, equipped with a measurable structure that is the Borel structure of its topology; let $\nu$ be an additive Haar measure on $E$. The assertion is that there exists $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that for every function $H \colon \mathrm{GL}_2(E) \to [0,\infty]$ that is measurable for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) of $\mathrm{GL}_2(E)$, the lower Lebesgue integral of $H$ against [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) — the Haar measure of the topological group $\mathrm{GL}_2(E)$ for that Borel structure, normalised so that the compact open set `semiLocalIntegralSet K L v` (which contains the identity) has measure one — equals $c$ times the integral, over $x \colon \mathrm{Fin}\,4 \to E$ with respect to the fourfold product measure $\nu^{\otimes 4}$, of the product of two factors: the value $H$ at the invertible matrix determined by $!![x_0,x_1;x_2,x_3]$ when its determinant is a unit of $E$ (and $0$ otherwise), and $\|N_{E/K_v}(x_0x_3-x_1x_2)\|^{-2}$, where $N_{E/K_v}$ is the algebra norm of $E$ over $K_v$ and $\|\cdot\|$ is the norm of $K_v$.
--
--   This identifies a Haar measure of $\mathrm{GL}_2$ over the semi-local algebra above a finite place in terms of the additive measure on matrix coordinates: the weight $|N_{E/K_v}(\det)|^{-2}$ turns $\nu^{\otimes 4}$ restricted to invertible matrices into a left Haar measure, and the normalising constant $c$ records the two normalisations. It is used in the estimate for twisted orbital integrals against the indicator of `semiLocalIntegralSet`, where integrals over $\mathrm{GL}_2(E)$ are computed in matrix coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ H : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] H →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          c * ∫⁻ x : Fin 4 → L ⊗[K] v.adicCompletion K,
            (if h : IsUnit (!![x 0, x 1; x 2, x 3] :
                Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
              ENNReal.ofReal
                ((‖Algebra.norm (v.adicCompletion K) (!![x 0, x 1; x 2, x 3] :
                    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => ν) := by sorry
