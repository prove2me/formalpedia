-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_lemma_5
-- name    : FlagshipMEA.Monopoly.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:43.463403+00:00
-- url     : https://prove2.me/theorems/07e1f2e1-f5b5-4eaa-8087-02d3615f234f
-- title:
--   Lemma 5 — a concentrated allocation minimizes cost at fixed effort
-- statement:
--   Assume the transformed cost $f_c(v)=c(\lambda\log v)$ is concave on the range used by feasible allocations. Fix total marketing effort $M\geq0$. For any product $i$ and any nonnegative allocation $m$ with $\sum_jm_j=M$, concentrating all effort on $i$ incurs no greater total cost:
--
--   $$\sum_j f_c\!\left(M\mathbf 1_{j=i}+e^{\theta/\lambda}\right)\leq\sum_j f_c(m_j+e^{\theta/\lambda}).$$
--
--   Thus every single-product allocation solves the fixed-effort cost minimization problem in equation (C–10). **Formalization Note** Concavity is imposed on $[e^{\theta/\lambda},\infty)$, the arguments actually reached by the program.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 41 (PDF 43), Lemma 5, (C–10); proof continued p. 42 (PDF 44)

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- Lemma 5 (p. 41): each concentrated allocation minimizes transformed cost
among all allocations with the same nonnegative total effort. -/
theorem lemma_5 {n : ℕ} (D : Data n) (hS : D.Standing)
    (hfc : D.FcConcave) (M : ℝ) (hM : 0 ≤ M) (i : Fin n) :
    ∀ m : Fin n → ℝ, Feasible m → tme m = M →
      D.cost (fun j => if j = i then M else 0) ≤ D.cost m := by sorry

end FlagshipMEA.Monopoly
