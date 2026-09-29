-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fcd7dad1-797e-5659-9f85-1c075c00e3b3
-- title:
--   Mixed logarithmic potential at a real place
-- statement:
--   Let $K$ be a number field, equipped on its infinite adele ring $K_\infty$ with a measurable structure that is Borel for the topology, and let $\lambda$ be an additive Haar measure on $K_\infty$. Let $\Psi \colon (\mathrm{Fin}\,3 \to \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}) \to \mathbb{C}$ be a function on triples of points of the mixed space of $K$ which is $C^\infty$ over $\mathbb{R}$ and has compact support, and assume there is a compact set $Ca$ of pairs of units of $K_\infty$ such that every $p$ in $\operatorname{tsupport}\Psi$ has its $0$th and $1$st coordinates of the form $\iota(q_1)$, $\iota(q_2)$ for some $(q_1,q_2)\in Ca$, where $\iota$ denotes the ring isomorphism `ringEquiv_mixedSpace` from $K_\infty$ to the mixed space. Let $w$ be an infinite place of $K$ which is real. Then there exist $A,B \colon (\mathrm{Fin}\,2 \to \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}) \to \mathbb{C}$, both $C^\infty$ over $\mathbb{R}$ and compactly supported, and a compact set of pairs of units of $K_\infty$ such that every point of $\operatorname{tsupport}A \cup \operatorname{tsupport}B$ is of the form $(\iota(q_1),\iota(q_2))$ with $(q_1,q_2)$ in that set, with the following property: for all units $a,t$ of $K_\infty$, the functions $x \mapsto \Psi(\iota t,\iota a,\iota x)$ and $x \mapsto \Psi(\iota t,\iota a,\iota x)\cdot\log\big(\|(1-t)_w\|^2+\|x_w\|^2\big)$ are $\lambda$-integrable, and $$\int_{K_\infty}\Psi(\iota t,\iota a,\iota x)\,\log\big(\|(1-t)_w\|^2+\|x_w\|^2\big)\,d\lambda(x) = A(\iota t,\iota a) + \|(1-t)_w\|\cdot B(\iota t,\iota a),$$ where $y \mapsto y_w$ is the evaluation ring homomorphism `archEval` from $K_\infty$ to the completion of $K$ at $w$.
--
--   This is the archimedean analytic input at a real place: the logarithmic potential $\log(\|1-t_w\|^2+\|x_w\|^2)$, integrated against a smooth compactly supported test function in the third adelic variable, is resolved into a smooth part and a term with the non-smooth factor $\|1-t_w\|$ carrying the singular behaviour, uniformly in the unit parameters $t,a$. It feeds the decomposition of the weighted archimedean distribution into orbital integrals together with real and complex place contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (Ψ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨc : HasCompactSupport Ψ)
    (hΨu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
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
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by sorry
