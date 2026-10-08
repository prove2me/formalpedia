-- Prove2me | Theorems.Thm_ExtADMM_Orth_lemma_2_3
-- name    : ExtADMM.Orth.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:37.218881+00:00
-- url     : https://prove2.me/theorems/637f2f03-ec49-4b44-a9d3-838aec3cc915
-- title:
--   Lemma 2.3, p. 7 — the three-term H inequality from k ≥ 1
-- statement:
--   Under the standing assumptions, $\beta>0$ and $A_1^TA_3=0$, consider any run of (2.4). Define $\tilde w^k=(x_1^{k+1},x_2^{k+1},x_3^{k+1},\lambda^{k+1}-\beta A_3(x_3^k-x_3^{k+1}))$. For $k\ge1$, the auxiliary point lies in $\Omega$ and, for every $w\in\Omega$,
--
--   $$\theta(w)-\theta(\tilde w^k)+(w-\tilde w^k)^TF(\tilde w^k)\ge\frac12\big(\|v-v^{k+1}\|_H^2-\|v-v^k\|_H^2\big)+\frac12\|v^k-v^{k+1}\|_H^2.$$
--
--   This telescoping inequality is the immediate source of the main theorem's contraction.
--
--   **Formalization Note.** The printed lemma claims every $k$, but its proof uses the previous iteration's $x_3$ optimality condition. An arbitrary initial point need not satisfy that condition, so the statement begins at $k=1$.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 7, Lemma 2.3, (2.13)–(2.14)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- Lemma 2.3, equation (2.14), p. 7, for k ≥ 1 as required by (2.19). -/
theorem lemma_2_3 {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β)
    (horth : P.A1.transpose * P.A3 = 0)
    (hrun : P.IsRun24 β x1 x2 x3 lam)
    (k : ℕ) (hk : 1 ≤ k) :
    P.wtilde β x1 x2 x3 lam k ∈ P.Omega ∧
      ∀ z ∈ P.Omega,
        (1 / 2 : ℝ) *
            (P.Hsq β (P.vs z - P.v x1 x3 lam (k + 1)) -
              P.Hsq β (P.vs z - P.v x1 x3 lam k)) +
          (1 / 2 : ℝ) * P.Hsq β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1)) ≤
          P.theta z - P.theta (P.wtilde β x1 x2 x3 lam k) +
            pair (z - P.wtilde β x1 x2 x3 lam k)
              (P.F (P.wtilde β x1 x2 x3 lam k)) := by sorry

end ExtADMM.Orth
