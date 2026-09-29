-- Prove2me | Theorems.Thm_AutomorphicForm_contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport
-- name    : AutomorphicForm.contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/c3520439-d1a6-559a-bdbd-70d5d2a934ac
-- title:
--   Smoothness and unit-carried support of |N_∞|^s-twists
-- statement:
--   Let $K$ be a number field and let $F\colon(\mathrm{Fin}\,2\to\mathbb{K}_\infty)\to\mathbb C$, where $\mathbb K_\infty$ denotes the mixed space `NumberField.mixedEmbedding.mixedSpace K`, be a function that is $C^\infty$ as a map of real vector spaces, has compact support, and whose closed support is carried by units in the following sense: there is a compact set $C_a\subseteq(\mathbb A_{K,\infty})^\times\times(\mathbb A_{K,\infty})^\times$ (units of the infinite adele ring) such that every $p\in\operatorname{tsupport}F$ is of the form $p=![\iota(q_1),\iota(q_2)]$ for some $q\in C_a$, with $\iota$ the ring isomorphism `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K` from the infinite adele ring to the mixed space. Let $s\in\mathbb R$. Then the function
--   $$p\longmapsto\Bigl(\prod_{w\mid\infty}\bigl\|\,(\iota^{-1}(p\,0))_w\,\bigr\|^{\,\mathrm{mult}(w)}\Bigr)^{s}\cdot F(p),$$
--   where the product is over the infinite places $w$ of $K$, the $w$-component is taken by the evaluation homomorphism [`NumberField.AdelicLevel.archEval K w`](def/NumberField_AdelicLevel.html#L137), $a\mapsto a_w\in K_w$, the real power is `Real.rpow` and the resulting real number is regarded as a complex scalar, is again $C^\infty$ over $\mathbb R$, has compact support, and has its closed support carried by units in exactly the same sense (for some compact $C_a$).
--
--   This is the stability of the class of smooth, compactly supported, unit-carried test functions on two copies of the mixed space under multiplication by the $s$-th power of the archimedean norm of the first coordinate; the case $s=-1/2$ supplies the renormalising factor $\prod_w\|t_w\|^{\mathrm{mult}(w)/2}$ used in the archimedean orbital-integral computations. It is cited in the assembly of the trace-formula identities [`AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex) and its twisted counterpart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem AutomorphicForm.contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport
    (K : Type) [Field K] [NumberField K]
    (F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F)
    (hFu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)])
    (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K =>
        ((((∏ w : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^ s
            : ℝ) : ℂ)) * F p) ∧
    HasCompactSupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K =>
        ((((∏ w : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^ s
            : ℝ) : ℂ)) * F p) ∧
    ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
      ∀ p ∈ tsupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K =>
        ((((∏ w : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^ s
            : ℝ) : ℂ)) * F p), ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by sorry
