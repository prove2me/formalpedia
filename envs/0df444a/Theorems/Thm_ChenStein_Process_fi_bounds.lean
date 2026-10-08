-- Prove2me | Theorems.Thm_ChenStein_Process_fi_bounds
-- name    : ChenStein.Process.fi_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:32:53.028854+00:00
-- url     : https://prove2.me/theorems/03196224-599e-418c-85f6-1aad1b10ebcc
-- title:
--   §6, p. 22 — ‖f_i‖ < 2(1 ∧ 1.4λ_i^{−1/2}) and ‖Δ_kf_i‖ < 4(1 ∧ 1.4λ_i^{−1/2}) for f_i = S_i(h − P_ih), ‖h‖ ≤ 1
-- statement:
--   Fix $d$, a coordinate $i$, and $\lambda_i>0$. Let $h:\mathbb Z_+^d\to\mathbb R$ satisfy $\|h\|=\sup_j|h(j)|\le1$, let $(P_ih)(j)=E\,h(j_1,\dots,Z_i,\dots,j_d)$ with $Z_i$ Poisson with mean $\lambda_i$, and put
--   $$f_i=S_i(h-P_ih).$$
--   Then, for every coordinate $k$,
--   $$\|f_i\|< 2\bigl(1\wedge1.4\lambda_i^{-1/2}\bigr),\qquad \|\Delta_kf_i\|< 4\bigl(1\wedge1.4\lambda_i^{-1/2}\bigr),$$
--   where $(\Delta_kf)(j)=f(j+e_k)-f(j)$.
--
--   These are the only bounds on the Stein solutions available in the multivariate argument; the factor $2$ in $\|\Delta_kf_i\|\le2\|f_i\|$ is what separates the constants of Theorem 2 from those of Theorem 1.
--
--   **Formalization Note** The strict sup-norm inequalities on the page are stated using the supremum of the nonempty, bounded range of absolute values, including points with $j_i=0$. Boundedness follows from $|h|\le1$ and the finite-parameter Poisson Stein solution. $\lambda_i^{-1/2}$ is the real power `λ_i ^ (-(1/2))`.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 22, §6, last sentence ("By Lemma 1 ... ‖f_i‖ < 2(1 ∧ 1.4λ_i^{−1/2}), so ‖Δ_kf_i‖ < 4(1 ∧ 1.4λ_i^{−1/2})")

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem fi_bounds {d : ℕ} (i : Fin d) (lj : ℝ≥0) (hlj : 0 < lj)
    (h : (Fin d → ℕ) → ℝ) (hh : ∀ j, |h j| ≤ 1) :
    let fi := Si i lj (h - Pi_ i lj h)
    sSup (Set.range (fun j : Fin d → ℕ => |fi j|)) <
        2 * min 1 (1.4 * (lj : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      ∀ k : Fin d, sSup (Set.range (fun j : Fin d → ℕ => |Δi k fi j|)) <
        4 * min 1 (1.4 * (lj : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end ChenStein.Process
