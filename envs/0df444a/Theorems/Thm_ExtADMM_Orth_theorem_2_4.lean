-- Prove2me | Theorems.Thm_ExtADMM_Orth_theorem_2_4
-- name    : ExtADMM.Orth.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:47.592982+00:00
-- url     : https://prove2.me/theorems/f38f003d-f4bc-46ec-bd95-db1dc4e2f523
-- title:
--   Theorem 2.4, p. 8 — orthogonal three-block ADMM contracts and converges
-- statement:
--   Let the three-block program satisfy its standing assumptions. Fix $\beta>0$, assume $A_1^TA_3=0$, and let $(w^k)$ be any run of the reordered direct ADMM scheme (2.4). For every $w^*\in\Omega^*$ and $k\ge1$,
--
--   $$\|v^{k+1}-v^*\|_H^2\le\|v^k-v^*\|_H^2-\|v^k-v^{k+1}\|_H^2.$$
--
--   If the joint map $[A_1,A_2]$ and $A_3$ have full column rank and $\Omega^*$ is nonempty, the complete four-block sequence $w^k$ converges to a point of $\Omega^*$, hence to a KKT point of (1.1). These are both parts of Theorem 2.4.
--
--   **Formalization Note.** The contraction starts at $k=1$ because the printed proof uses a previous-iteration optimality condition. The convergence part explicitly assumes a KKT point exists: existence of a primal optimizer on p. 1 alone does not imply it. Full column rank of $[A_1,A_2]$ is injectivity of $(u_1,u_2)\mapsto A_1u_1+A_2u_2$.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 8, Theorem 2.4, (2.22)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- Theorem 2.4, p. 8, both parts. The contraction starts at k ≥ 1; part (ii)
    assumes Ω* is nonempty because a primal solution alone does not provide a KKT point. -/
theorem theorem_2_4 {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β)
    (horth : P.A1.transpose * P.A3 = 0)
    (hrun : P.IsRun24 β x1 x2 x3 lam) :
    (∀ ws ∈ P.OmegaStar, ∀ k : ℕ, 1 ≤ k →
      P.Hsq β (P.v x1 x3 lam (k + 1) - P.vs ws) ≤
        P.Hsq β (P.v x1 x3 lam k - P.vs ws) -
          P.Hsq β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))) ∧
    (P.Blocks12Injective → Function.Injective P.A3.mulVec → P.OmegaStar.Nonempty →
      ∃ ws ∈ P.OmegaStar,
        Filter.Tendsto (fun k : ℕ => (x1 k, x2 k, x3 k, lam k))
          Filter.atTop (nhds (ws.x1, ws.x2, ws.x3, ws.lam))) := by sorry

end ExtADMM.Orth
