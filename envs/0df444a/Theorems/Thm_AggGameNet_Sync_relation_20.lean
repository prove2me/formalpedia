-- Prove2me | Theorems.Thm_AggGameNet_Sync_relation_20
-- name    : AggGameNet.Sync.relation_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:36.372965+00:00
-- url     : https://prove2.me/theorems/d1149aef-0cee-4d1e-9b33-9c3264850e7e
-- title:
--   Relation (20), p. 14 — weighted aggregate-estimate errors are summable
-- statement:
--   Let $(x^k,v^k)$ be the synchronous run under Assumptions 1, 3–6, including the positive weight floor and global aggregate Lipschitz condition. For each player $i$,
--
--   $$\sum_{k=0}^{\infty}\alpha_k\|\hat v_i^k-y^k\|<\infty.$$
--
--   This is the summability condition used to apply the deterministic convergence lemma to relation (19).
--
--   **Formalization Note** Assumption 2 is unnecessary for this estimate. Assumption 3 is extended to all aggregate arguments because the algorithm uses $N\hat v_i^k$.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, relation (20), proof of Proposition 2, p. 14

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

/-- Relation (20), proof of Proposition 2, p. 14. -/
theorem relation_20 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (h6 : Assumption6 α)
    (x v : ℕ → Fin N → E n) (hrun : IsSyncRun K F W α x v) :
    ∀ i, Summable (fun k => α k * ‖vhat W v k i - yavg v k‖) := by sorry

end AggGameNet.Sync
