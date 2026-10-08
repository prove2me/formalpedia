-- Prove2me | Theorems.Thm_ExtADMM_Orth_eq_2_24_to_2_26
-- name    : ExtADMM.Orth.eq_2_24_to_2_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:02.427517+00:00
-- url     : https://prove2.me/theorems/11c84840-1239-4a91-884f-814a3b8c33c4
-- title:
--   (2.24)–(2.26), p. 8 — summable H steps and vanishing Q correction
-- statement:
--   Assume the standing three-block hypotheses, $\beta>0$, $A_1^TA_3=0$, a run of (2.4), and at least one solution of $\mathrm{VI}(\Omega,F,\theta)$. The squared $H$ steps are summable from the paper's starting index, and the four-block $Q$ correction tends to zero:
--
--   $$\sum_{k=1}^{\infty}\|v^k-v^{k+1}\|_H^2<\infty,\qquad Q(v^k-v^{k+1})\longrightarrow0.$$
--
--   These assertions give the asymptotic input for the cluster-point variational inequality. The intervening printed formula $H(v^k-v^{k+1})\to0$ is left as the bridge between them.
--
--   **Formalization Note.** Summability is expressed on the shifted sequence indexed by $k=0$, representing the paper's $k=1$ start. The four components of $Q\Delta v$ converge separately.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 8, (2.24)–(2.26)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- Equations (2.24)–(2.26), p. 8, with the series starting at k = 1. -/
theorem eq_2_24_to_2_26 {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β)
    (horth : P.A1.transpose * P.A3 = 0)
    (hrun : P.IsRun24 β x1 x2 x3 lam)
    (hstar : P.OmegaStar.Nonempty) :
    Summable (fun k : ℕ =>
      P.Hsq β (P.v x1 x3 lam (k + 1) - P.v x1 x3 lam (k + 2))) ∧
    Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).x1)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).x2)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).x3)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).lam)
      Filter.atTop (nhds 0) := by sorry

end ExtADMM.Orth
