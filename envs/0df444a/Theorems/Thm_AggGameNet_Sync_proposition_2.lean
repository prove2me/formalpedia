-- Prove2me | Theorems.Thm_AggGameNet_Sync_proposition_2
-- name    : AggGameNet.Sync.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:24.332634+00:00
-- url     : https://prove2.me/theorems/abfc629b-684e-4ed6-a91d-a026af56bf55
-- title:
--   Proposition 2, p. 13 — synchronous iterates converge to the unique VI solution
-- statement:
--   Consider $N\ge1$ players with nonempty compact convex strategy sets $K_i$, a continuous aggregate field $F_i$, and strictly monotone $\phi_i(x)=F_i(x_i,\sum_jx_j)$. Suppose each $F_i(x_i,\cdot)$ has a positive uniform Lipschitz constant $\bar L_i$, every window of $Q$ communication graphs is connected, the neighbour-supported matrices $W(k)$ are doubly stochastic with a positive lower weight $\delta$, and the stepsizes decrease with $\sum_k\alpha_k=\infty$ and $\sum_k\alpha_k^2<\infty$. Start from $x_i^0\in K_i$, set $v_i^0=x_i^0$, and follow the synchronous projected-gradient updates (9)–(11). Then the variational inequality has exactly one solution $x^*$, and
--
--   $$x^k\longrightarrow x^*.$$
--
--   This establishes convergence of the distributed algorithm despite each player using a local estimate of the aggregate.
--
--   **Formalization Note** Assumption 3 is extended from $\bar K$ to every aggregate argument because $N\hat v_i^k$ need not lie in $\bar K$. The positive lower weight $\delta>0$ and nonemptiness of $K_i$ are explicit. Convergence is in the finite product topology; the conclusion asserts existence and uniqueness, avoiding a vacuous conditional claim.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Proposition 2, p. 13

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

open Filter
open scoped Topology

/-- Proposition 2, p. 13: convergence to the unique solution of `VI(K, φ)`. -/
theorem proposition_2 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (h2 : Assumption2 K F)
    (Lbar : Fin N → ℝ) (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (h6 : Assumption6 α)
    (x v : ℕ → Fin N → E n) (hrun : IsSyncRun K F W α x v) :
    ∃ xs, IsVISol K F xs ∧
      (∀ y, IsVISol K F y → y = xs) ∧ Tendsto x atTop (𝓝 xs) := by sorry

end AggGameNet.Sync
