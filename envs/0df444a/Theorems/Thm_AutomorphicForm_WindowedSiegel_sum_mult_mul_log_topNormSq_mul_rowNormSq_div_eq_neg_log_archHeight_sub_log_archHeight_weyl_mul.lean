-- Prove2me | Theorems.Thm_AutomorphicForm_WindowedSiegel_sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul
-- name    : AutomorphicForm.WindowedSiegel.sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/9faa3f30-0121-550a-af9c-6f7f5968bbb1
-- title:
--   Weight bridge: sum_w m_wlog(topcdotrow/‖det‖²) versus archimedean heights
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$ and infinite adele ring $K_\infty$. The assertion is an equality of two real-valued functions on $\mathrm{GL}_2(K_\infty)$. The first sends $x$ to $\sum_{w} m_w \log\bigl(\mathrm{topNormSq}(x_w)\,\mathrm{rowNormSq}(x_w)/\|\det x_w\|^2\bigr)$, the sum being over the infinite places $w$ of $K$, where $m_w$ is the multiplicity `InfinitePlace.mult` of $w$, where $x_w$ denotes the matrix underlying the image of $x$ in $\mathrm{GL}_2(K_w)$ under `archComponent` (the functorial image along evaluation of an infinite adele at $w$), and where for a $2\times 2$ matrix $g$ one puts $\mathrm{topNormSq}(g)=\|g_{00}\|^2+\|g_{01}\|^2$ and $\mathrm{rowNormSq}(g)=\|g_{10}\|^2+\|g_{11}\|^2$. The second sends $y$ to $-\log \mathrm{archHeight}(y)-\log \mathrm{archHeight}(\omega\, y)$, where $\mathrm{archHeight}(g)=\prod_{w}\bigl(\|\det g_w\|/\mathrm{rowNormSq}(g_w)\bigr)^{m_w}$ and $\omega\in\mathrm{GL}_2(K_\infty)$ is the image under `glArch` of `adelicWeyl`, that is, the image of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}\in\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb A_K)$ under the structure map, projected to the infinite component.
--
--   This identifies two spellings of the archimedean weight factor occurring in weighted orbital integrals on $\mathrm{GL}_2$ over a number field: the explicit sum over infinite places of logarithms of $\mathrm{topNormSq}\cdot\mathrm{rowNormSq}/\|\det\|^2$, and the height expression $-\log H_\infty(x)-\log H_\infty(\omega x)$ built from the Weyl element. It is used by the constructions of compactly supported test functions matching prescribed archimedean weights and by the identification of weighted orbital integrals on scalar multiples of diagonal tori.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindowedSiegel_sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.WindowedSiegel.sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul
    (K : Type) [Field K] [NumberField K] :
    (fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2))) =
    (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
                  (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) := by sorry
