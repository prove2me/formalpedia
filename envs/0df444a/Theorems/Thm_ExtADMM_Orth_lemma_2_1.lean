-- Prove2me | Theorems.Thm_ExtADMM_Orth_lemma_2_1
-- name    : ExtADMM.Orth.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:37.6388+00:00
-- url     : https://prove2.me/theorems/f257b3fd-56ac-4590-b03d-b60863bb135f
-- title:
--   Lemma 2.1, p. 5 — the output of (2.4) satisfies the Q variational inequality
-- statement:
--   For a three-block problem satisfying the standing assumptions, let $\beta>0$ and let $(w^k)$ be any run of the reordered ADMM scheme (2.4). At each iteration $k\ge0$, its output $w^{k+1}$ lies in $\Omega$ and, for every $w\in\Omega$,
--
--   $$\theta(w)-\theta(w^{k+1})+(w-w^{k+1})^T\{F(w^{k+1})+Q(v^k-v^{k+1})\}\ge0.$$
--
--   Here $v^k=(x_1^k,x_3^k,\lambda^k)$ and $Q$ is the four-by-three block matrix in (2.9), including the coefficient $-1/\beta$ in its final diagonal block. This inequality records the first-order information of one complete update cycle. The lemma itself needs no $A_1^TA_3=0$ hypothesis.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 5, Lemma 2.1, (2.8)–(2.9)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- Lemma 2.1, equation (2.8), p. 5. -/
theorem lemma_2_1 {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β) (hrun : P.IsRun24 β x1 x2 x3 lam)
    (k : ℕ) :
    P.w x1 x2 x3 lam (k + 1) ∈ P.Omega ∧
      ∀ z ∈ P.Omega,
        0 ≤ P.theta z - P.theta (P.w x1 x2 x3 lam (k + 1)) +
          pair (z - P.w x1 x2 x3 lam (k + 1))
            (P.F (P.w x1 x2 x3 lam (k + 1)) +
              P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))) := by sorry

end ExtADMM.Orth
