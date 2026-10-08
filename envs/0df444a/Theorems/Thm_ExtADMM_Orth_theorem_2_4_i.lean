-- Prove2me | Theorems.Thm_ExtADMM_Orth_theorem_2_4_i
-- name    : ExtADMM.Orth.theorem_2_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:45.394986+00:00
-- url     : https://prove2.me/theorems/ba151cb4-e2d4-41c1-9cb7-e3b44edd10b2
-- title:
--   Theorem 2.4(i), (2.22), p. 8 — contraction relative to every VI solution
-- statement:
--   Let the standing assumptions hold, $\beta>0$, $A_1^TA_3=0$, and let $(w^k)$ be a run of (2.4). For every variational inequality solution $w^*\in\Omega^*$ and its essential projection $v^*=(x_1^*,x_3^*,\lambda^*)$, the essential iterates satisfy, for every $k\ge1$,
--
--   $$\|v^{k+1}-v^*\|_H^2\le\|v^k-v^*\|_H^2-\|v^k-v^{k+1}\|_H^2.$$
--
--   The result is the quantitative Fejér-type estimate used to control the essential states. $H$ is positive semidefinite, so this is a seminorm estimate.
--
--   **Formalization Note.** The printed index includes $k=0$, but Lemma 2.3 and the paper's own sum (2.24) justify the assertion from $k=1$.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 8, Theorem 2.4(i), (2.22)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- Theorem 2.4(i), (2.22), p. 8, for k ≥ 1. -/
theorem theorem_2_4_i {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β)
    (horth : P.A1.transpose * P.A3 = 0)
    (hrun : P.IsRun24 β x1 x2 x3 lam) :
    ∀ ws ∈ P.OmegaStar, ∀ k : ℕ, 1 ≤ k →
      P.Hsq β (P.v x1 x3 lam (k + 1) - P.vs ws) ≤
        P.Hsq β (P.v x1 x3 lam k - P.vs ws) -
          P.Hsq β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1)) := by sorry

end ExtADMM.Orth
