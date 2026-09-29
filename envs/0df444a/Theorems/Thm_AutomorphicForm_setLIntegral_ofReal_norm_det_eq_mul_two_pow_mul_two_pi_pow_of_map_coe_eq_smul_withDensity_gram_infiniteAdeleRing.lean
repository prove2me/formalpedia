-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
-- name    : AutomorphicForm.setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9eb486e5-be5f-549b-94e7-84ebd809885e
-- title:
--   Archimedean constant of the Gram-normalised measure on GL₂
-- statement:
--   Let $K$ be a number field, write $K_\infty$ for `InfiniteAdeleRing K`, and let $\tau_a$ be a measure on $\mathrm{GL}_2(K_\infty)$ for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57). Let $n\in\mathbb N$, let $e\colon \mathrm{Fin}\,n\to M_2(K_\infty)$ and let $s\in[0,\infty]$. The hypothesis `harch` is stated with $K_\infty$ made an $\mathbb R$-algebra by transporting the algebra map $\mathbb R\to$ mixed space of $K$ along the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace K`, and with Borel $\sigma$-algebras on $M_2(K_\infty)$ and $\mathrm{GL}_2(K_\infty)$; it asserts that $e$ is $\mathbb R$-linearly independent, that its range spans $M_2(K_\infty)$ over $\mathbb R$, and that the image of $\tau_a$ under the inclusion $\mathrm{GL}_2(K_\infty)\subset M_2(K_\infty)$ is $s$ times the measure obtained as follows: push Lebesgue measure on $\mathbb R^n$ forward along $c\mapsto\sum_i c_ie_i$, scale by $\sqrt{|\det(\mathrm{Tr}_{K_\infty/\mathbb R}\,\mathrm{tr}(e_ie_j))_{i,j}|}$, and weight by the density $X\mapsto |N_{K_\infty/\mathbb R}(\det X)|^{-2}$. Let further $y\colon M_2(K_\infty)\to$ mixed space of $K$ be Borel measurable and satisfy $y(g\cdot n(x))=y(g)+\mathrm{ringEquiv\_mixedSpace}(x)$ for all $g\in\mathrm{GL}_2(K_\infty)$ and $x\in K_\infty$, where $n(x)=\mathrm{AutomorphicForm.unipotentGL2}\,x=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then the lower Lebesgue integral of $g\mapsto \|\det g\|$ (as a nonnegative extended real) against $\tau_a$, over the set of $g$ such that $y(g)$ lies in the unit cube (each real coordinate in $[0,1]$, each complex coordinate with real and imaginary part in $[0,1]$), such that for $i=0,1$ the image of the entry $g_{i0}$ in the mixed space lies in that same unit cube, and such that $\|(\det g)_w\|\in[1,e]$ at every infinite place $w$ of $K$, equals $s\cdot 2^{4r_2+r_1}\,(2\pi)^{r_2}$, with $r_1$ the number of real and $r_2$ the number of complex places of $K$.
--
--   This is the archimedean factor of the constant occurring in Weil's integration formula for $\mathrm{GL}_2$ relative to the unipotent radical of the mirabolic subgroup, computed for a Haar measure normalised by the Gram determinant of the trace form on $M_2(K_\infty)$ and the test region given by two unit cubes and the determinant shell $1\le\|\det\|\le e$. It feeds the global computation [`AutomorphicForm.measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one`](thm.html#AutomorphicForm.measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one), where the constant is matched against a value of the Dedekind zeta function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

open scoped Classical in

theorem AutomorphicForm.setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K]
    (τa : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))

    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        Submodule.span ℝ (Set.range e) = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)| ^ 2)⁻¹))

    (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) → mixedEmbedding.mixedSpace K)
    (hy : Measurable[borel _] y)
    (hy1 : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (x : InfiniteAdeleRing K),
      y ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
        y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) + InfiniteAdeleRing.ringEquiv_mixedSpace K x) :
    ∫⁻ g in {g : GL (Fin 2) (InfiniteAdeleRing K) |
        ((∀ w : {w : InfinitePlace K // w.IsReal},
              (y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ i : Fin 2,
          (∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K
                ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0)).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K
                  ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0)).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K
                  ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0)).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ w : InfinitePlace K,
          ‖((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ∈
            Set.Icc (1 : ℝ) (Real.exp 1)},
      ENNReal.ofReal
        ‖((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ ∂τa =
      s * (2 ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
        ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K)) := by sorry
