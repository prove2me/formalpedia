-- Prove2me | Theorems.Thm_ExtADMM_Orth_lemma_2_2
-- name    : ExtADMM.Orth.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:36.519001+00:00
-- url     : https://prove2.me/theorems/42b2144a-9ba5-4475-87ac-b06ddc9f6a21
-- title:
--   Lemma 2.2, p. 6 — the H lower bound with the A₃ correction
-- statement:
--   Suppose the standing three-block assumptions hold, $\beta>0$, $A_1^TA_3=0$, and $(w^k)$ is a run of (2.4). For every $k\ge0$, $w^{k+1}\in\Omega$ and for every $w\in\Omega$,
--
--   $$\theta(w)-\theta(w^{k+1})+(w-w^{k+1})^T\{F(w^{k+1})+\beta PA_3(x_3^k-x_3^{k+1})\}\ge (v-v^{k+1})^TH(v^k-v^{k+1}).$$
--
--   The block matrix $H$ is (2.11), with $\beta A_1^TA_1$ and $\beta A_3^TA_3$ on its leading diagonal blocks, $-A_1^T$ and $-A_1$ off diagonal, and $1/\beta$ on its multiplier block. This inequality is the source of the contraction estimate.
--
--   **Formalization Note.** The displayed opening of Lemma 2.2 prints $x_1^k$ in $w^{k+1}$; the update and its inequality require $x_1^{k+1}$, which is used here.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 6, Lemma 2.2, (2.10)–(2.11)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- Lemma 2.2, equation (2.10), p. 6; the printed x₁ᵏ in the displayed wᵏ⁺¹ is x₁ᵏ⁺¹. -/
theorem lemma_2_2 {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β)
    (horth : P.A1.transpose * P.A3 = 0)
    (hrun : P.IsRun24 β x1 x2 x3 lam) (k : ℕ) :
    P.w x1 x2 x3 lam (k + 1) ∈ P.Omega ∧
      ∀ z ∈ P.Omega,
        P.Hform β (P.vs z - P.v x1 x3 lam (k + 1))
          (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1)) ≤
          P.theta z - P.theta (P.w x1 x2 x3 lam (k + 1)) +
            pair (z - P.w x1 x2 x3 lam (k + 1))
              (P.F (P.w x1 x2 x3 lam (k + 1)) +
                P.PA3 β (x3 k - x3 (k + 1))) := by sorry

end ExtADMM.Orth
