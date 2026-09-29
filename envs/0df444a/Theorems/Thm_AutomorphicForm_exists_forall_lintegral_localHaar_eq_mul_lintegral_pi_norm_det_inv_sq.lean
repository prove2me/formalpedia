-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
-- name    : AutomorphicForm.exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/9fd59c6f-3d58-5565-b97c-356f8d75c34b
-- title:
--   Haar measure on GL₂(Kᵥ) in matrix coordinates
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, i.e. a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, and let $F = K_v$ be the associated adic completion, equipped with a measurable space structure which is the Borel structure of its topology. Let $\mu$ be an additive Haar measure on $F$. The assertion is the existence of a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that for every function $H \colon \mathrm{GL}_2(F) \to [0,\infty]$ which is measurable for the Borel $\sigma$-algebra [`AutomorphicForm.localGLBorel K v`](def/AutomorphicForm_LocalOrbitalBase.html#L154) of the topology of $\mathrm{GL}_2(F)$, the lower Lebesgue integral of $H$ against [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) — the left Haar measure on $\mathrm{GL}_2(F)$ for that Borel structure normalised so as to give mass $1$ to the compact set with nonempty interior `localIntegralSet K v` — equals $c$ times the integral over $F^4$, with respect to the fourfold product measure $\mu^{\otimes 4}$, of the function sending $x = (x_0,x_1,x_2,x_3)$ to $H\!\left(\begin{smallmatrix} x_0 & x_1 \\ x_2 & x_3\end{smallmatrix}\right) \cdot \|\det x\|^{-2}$ when $\det\left(\begin{smallmatrix} x_0 & x_1 \\ x_2 & x_3\end{smallmatrix}\right) \neq 0$ (the matrix being viewed as an element of $\mathrm{GL}_2(F)$ via `Matrix.GeneralLinearGroup.mkOfDetNeZero`) and to $0$ otherwise, the density being taken as a nonnegative extended real via `ENNReal.ofReal`.
--
--   This is the standard coordinate description of a Haar measure on $\mathrm{GL}_2$ of a local field: on the open subset $\{\det \neq 0\}$ of the space $M_2(F) \cong F^4$ of matrices, the measure $\|\det x\|^{-2}\,d\mu^{\otimes 4}(x)$ is a Haar measure, hence agrees with the normalised Haar measure of the group up to a finite positive factor. It is the basis for the explicit evaluation of local orbital integrals, and is used in the computation of orbital integrals of elements of the local centralizer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

theorem AutomorphicForm.exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localGLBorel K v
         ∫⁻ g, H g ∂(AutomorphicForm.localHaar K v)) =
          c * ∫⁻ x : Fin 4 → v.adicCompletion K,
            (if h : (!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal
                ((‖(!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => μ) := by sorry
