-- Prove2me | Theorems.Thm_ExtADMM_Orth_eq_2_27
-- name    : ExtADMM.Orth.eq_2_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:20.590574+00:00
-- url     : https://prove2.me/theorems/39719c66-d579-43f4-b7ad-43122bffed28
-- title:
--   (2.27), p. 8 — every convergent output subsequence has a KKT limit
-- statement:
--   Let $(w^k)$ be a run of (2.4) under the standing assumptions and $\beta>0$. Suppose $Q(v^k-v^{k+1})\to0$. If a strictly increasing sequence of indices selects outputs $w^{k+1}$ converging to $w^\infty$, then
--
--   $$w^\infty\in\Omega,\qquad \theta(w)-\theta(w^\infty)+(w-w^\infty)^TF(w^\infty)\ge0\quad\text{for every }w\in\Omega.$$
--
--   Thus every such cluster point is a KKT point in the paper's variational inequality sense. This result isolates the limiting step from the separate task of proving that a convergent subsequence exists.
--
--   **Formalization Note.** Closedness of the three constraint sets and continuity of the real-valued convex objectives are supplied by the standing assumptions. Given the vanishing $Q$ correction, orthogonality is not needed.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 8, (2.27)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- The cluster-point assertion (2.27), p. 8, with its asymptotic input explicit. -/
theorem eq_2_27 {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β)
    (hrun : P.IsRun24 β x1 x2 x3 lam)
    (hQ1 : Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).x1)
      Filter.atTop (nhds 0))
    (hQ2 : Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).x2)
      Filter.atTop (nhds 0))
    (hQ3 : Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).x3)
      Filter.atTop (nhds 0))
    (hQlam : Filter.Tendsto (fun k : ℕ =>
      (P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))).lam)
      Filter.atTop (nhds 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (winf : Pt n1 n2 n3 p)
    (hlim : Filter.Tendsto
      (fun j : ℕ => (x1 (φ j + 1), x2 (φ j + 1), x3 (φ j + 1), lam (φ j + 1)))
      Filter.atTop (nhds (winf.x1, winf.x2, winf.x3, winf.lam))) :
    winf ∈ P.OmegaStar := by sorry

end ExtADMM.Orth
