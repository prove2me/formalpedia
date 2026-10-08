-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_corollary_4_1
-- name    : ConstrainedQueueing.Nonstationary.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:27.957973+00:00
-- url     : https://prove2.me/theorems/6302f266-b8ce-40cc-9486-8c37a307ddbc
-- title:
--   Corollary 4.1, p. 1942 — one ε > 0 with Σ_{l∈W_af} a_l − ε ≥ Σ_{W_af→W′_af} f for all f ∈ co(S) and all mincuts
-- statement:
--   Let the constraint set $S$ satisfy C.1 and contain the empty activation set, and let $a\ge0$ with $a\notin\bar C'$. Then there is an $\epsilon>0$ such that for every $f\in\mathrm{co}(S)$ and every minimum cut $(W,W')_{af}$ of the flow network $N_{af}$, with $W_{af}$ its set of queues on the originator's side,
--   $$\sum_{l\in W_{af}}a_l-\epsilon\ \ge\ \sum_{\substack{i\in W_{af},\ j\in W'_{af}\\ i\ne o,\ (i,j)\in E}}f_{(i,j)} .$$
--   The right-hand side is the total capacity of the server edges leaving $W_{af}$, including the edges into the terminal $d$ (servers that send customers out of the system).
--
--   The constant $\epsilon$ is chosen before $f$: it is one margin, uniform over the convex hull of the activation vectors. It is the drift that, in the proof of Theorem 4.1, makes the number of customers in the set of queues $W_{a\lambda(t)}$ grow linearly.
--
--   **Formalization Note.** A cut is represented by the set `W` of queues on the originator's side, and the statement quantifies over every `W` that is a mincut (`IsMinCut`), since the page's $(W,W')_{af}$ is an arbitrary mincut. The server edges from $W$ to $W'$ are the servers $k$ with $q(k)\in W$ and $h(k)\notin W$ or $h(k)$ out of the system. As in Lemma 4.1, the page's $(\bar C)^c$ is read as $(\bar C')^c$, and $\emptyset\in S$, $a\ge0$ are standing conventions.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1942, §IV, Corollary 4.1

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

namespace ConstrainedQueueing.Nonstationary

/-- Corollary 4.1 (p. 1942): if the nonnegative rate vector `a` lies outside the closure of
`C'`, there is one `ε > 0` such that for every `f ∈ co(S)` and every mincut `(W, W')` of
`N_af`, the arrival rates into the queues of `W` exceed by at least `ε` the total capacity of
the server edges directed from `W` to `W'`. -/
theorem corollary_4_1 {L N : ℕ} (net : Network L N) (hC1 : C1 net)
    (hS0 : (∅ : Finset (Fin N)) ∈ net.S)
    (a : Fin L → ℝ) (ha0 : 0 ≤ a) (ha : a ∉ closure (Cprime net)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ coS net, ∀ W : Finset (Fin L), IsMinCut net a f W →
      ∑ l ∈ W, a l - ε ≥ ∑ i ∈ serverOut net W, f i := by sorry

end ConstrainedQueueing.Nonstationary
