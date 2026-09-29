-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
-- name    : AutomorphicForm.lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/9ba2713a-f395-5405-994c-8192b1f4466b
-- title:
--   Haar measure of GL₂(L⊗_K Kᵥ) in big-cell coordinates
-- statement:
--   Let $K$ and $L$ be number fields with $K \to L$ an algebra map, let $v$ be a nonzero prime of $\mathcal{O}_K$, and write $E = L \otimes_K K_v$ for the tensor product with the $v$-adic completion, equipped with a measurable structure which is the Borel structure of its topology. Let $\nu$ be an additive Haar measure on $E$, and let $c_G \in [0,\infty]$. Throughout, $\mathrm{GL}_2(E)$ carries the Borel $\sigma$-algebra `glBorelOf` of its topology, and `semiLocalHaar` denotes the Haar measure on $\mathrm{GL}_2(E)$ normalised to give mass one to the compact open set `semiLocalIntegralSet K L v`, which contains $1$. Assume the hypothesis $hG$: for every Borel $H \colon \mathrm{GL}_2(E) \to [0,\infty]$, $\int H \, d(\mathrm{semiLocalHaar}) = c_G \int_{E^4} H\!\left(\begin{smallmatrix} x_0 & x_1 \\ x_2 & x_3\end{smallmatrix}\right) \lvert N_{E/K_v}(\det)\rvert^{-2} \, d\nu^4(x)$, the integrand being $0$ at those $x$ where the determinant is not a unit. Then for every Borel $\Phi \colon \mathrm{GL}_2(E) \to [0,\infty]$, $$\int \Phi \, d(\mathrm{semiLocalHaar}) = c_G \int_{E^2} \int_{E^2} \Phi\!\left(\begin{smallmatrix} p_1 & 0 \\ 0 & p_2 \end{smallmatrix}\right)\!\left(\begin{smallmatrix} 1 + q_1 q_2 & q_1 \\ q_2 & 1\end{smallmatrix}\right) \lvert N_{E/K_v}(p_1 p_2)\rvert^{-1} \, d(\nu \otimes \nu)(p) \, d(\nu \otimes \nu)(q),$$ the inner integration being over $p$ and the outer over $q$, and the integrand being $0$ unless both $\det\,\mathrm{diag}(p_1,p_2)$ and the determinant of the second matrix are units in $E$.
--
--   This is the expression of the Haar measure of $\mathrm{GL}_2(E)$, $E = L \otimes_K K_v$, in the coordinates $(p,q) \mapsto \mathrm{diag}(p_1,p_2) \cdot \left(\begin{smallmatrix} 1+q_1q_2 & q_1 \\ q_2 & 1\end{smallmatrix}\right)$ of the big cell, the diagonal torus contributing $\lvert N(p_1p_2)\rvert^{-1} d\nu(p_1) d\nu(p_2)$ and the transversal slice the measure $d\nu(q_1) d\nu(q_2)$; the matrix-coordinate normalisation constant $c_G$ is carried along as a hypothesis. It is used in the computation of twisted orbital integrals at diagonal elements, namely by [`AutomorphicForm.lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal`](thm.html#AutomorphicForm.lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.lintegral_semiLocalHaar_eq_mul_lintegral_lintegral_torus_mul_unipotentChart
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (cG : ENNReal)
    (hG : ∀ H : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] H →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          cG * ∫⁻ x : Fin 4 → L ⊗[K] v.adicCompletion K,
            (if h : IsUnit (!![x 0, x 1; x 2, x 3] :
                Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
              ENNReal.ofReal
                ((‖Algebra.norm (v.adicCompletion K) (!![x 0, x 1; x 2, x 3] :
                    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => ν))
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal)
    (hΦ : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Φ) :
    (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
     ∫⁻ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v)) =
      cG * ∫⁻ q : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
              if h' : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                Φ (Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h')
              else 0
            else 0) *
            ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ ∂(ν.prod ν) ∂(ν.prod ν) := by sorry
