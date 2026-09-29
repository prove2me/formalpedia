-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_sq_mul_log_mul_of_isComplex
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_sq_mul_log_mul_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/56995849-1a72-5698-aa96-fce49364b8ea
-- title:
--   Archimedean logarithmic potential at a complex place
-- statement:
--   Let $K$ be a number field, let the infinite adele ring $K_\infty$ carry a Borel measurable structure, and let $\lambda$ be an additive Haar measure on $K_\infty$. Let $\Psi$ be a $\mathbb{C}$-valued function on triples of points of the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $K$, smooth of class $C^\infty$ over $\mathbb{R}$ and of compact support, and assume there is a compact set $C_a$ of pairs of units of $K_\infty$ such that every $p$ in the closed support of $\Psi$ has $p_0$ and $p_1$ equal to the images under the ring isomorphism $K_\infty\cong\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of the two components of some pair in $C_a$. Let $w$ be an infinite place of $K$ which is complex. Then there are functions $A,B$ on pairs of points of the mixed space, both $C^\infty$ and compactly supported, and a compact set of pairs of units of $K_\infty$ such that every point of $\operatorname{tsupport}A\cup\operatorname{tsupport}B$ is exactly the pair of images of the components of some pair in that set, with the following property: for all units $a,t$ of $K_\infty$, writing $\iota$ for the above isomorphism and $z_w$ for the $w$-component of $z\in K_\infty$, both $x\mapsto\Psi(\iota t,\iota a,\iota x)$ and its product with $\log(\|(1-t)_w\|^2+\|x_w\|^2)$ are $\lambda$-integrable, and $$\int_{K_\infty}\Psi(\iota t,\iota a,\iota x)\,\log\bigl(\|(1-t)_w\|^2+\|x_w\|^2\bigr)\,d\lambda(x)=A(\iota t,\iota a)+\|(1-t)_w\|^2\log\|(1-t)_w\|\cdot B(\iota t,\iota a).$$
--
--   This is the complex-place case of the archimedean logarithmic-potential estimate: integration of a smooth compactly supported test function against $\log(\|1-t_w\|^2+\|x_w\|^2)$ in the adelic variable $x$ produces a smooth compactly supported main term plus the explicit singular factor $\|1-t_w\|^2\log\|1-t_w\|$ times a second smooth compactly supported function. It feeds the archimedean part of the expansion recorded in [`AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex), the proof transporting $\lambda$ to Lebesgue measure on the mixed space, splitting off the $w$-coordinate and applying the one-variable parametric statement [`MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport`](thm.html#MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_sq_mul_log_mul_of_isComplex.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_sq_mul_log_mul_of_isComplex
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (Ψ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨc : HasCompactSupport Ψ)
    (hΨu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ),
        Integrable (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x]) lam ∧
        Integrable (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
            ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ)) lam ∧
        ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
            ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ) ∂lam =
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by sorry
