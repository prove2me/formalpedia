-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_display_4_7
-- name    : ConstrainedQueueing.Nonstationary.display_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:21.263986+00:00
-- url     : https://prove2.me/theorems/c8e07fc7-9d3b-4493-9624-1c98213fd0d0
-- title:
--   (4.7), proof of Theorem 4.1, p. 1942 — Σ_l X_l(t) ≥ min_Q Σ_{τ=1}^t (Σ_{l∈Q}(A_l(τ) − a_l) + ε), pathwise
-- statement:
--   Fix a single-class network, a rate vector $a\in\mathbb R^L$ and a number $\epsilon$ with the property of Corollary 4.1: for every $f\in\mathrm{co}(S)$ and every mincut $(W,W')_{af}$ of $N_{af}$, $\sum_{l\in W_{af}}a_l-\epsilon\ge\sum_{W_{af}\to W'_{af}}f$ (sum over the server edges leaving $W_{af}$). Let $\pi\in\tilde G$ be an admissible history-dependent policy, $X(0)$ any initial state, $A_l(\tau)$ any sequence of arrivals, and $X(t)$ the resulting queue lengths, following (2.1) with one-slot service. Then for every $t\ge0$
--   $$\sum_{l=1}^L X_l(t)\ \ge\ \min_{Q\subseteq\{1,\dots,L\}}\Big\{\sum_{\tau=1}^{t}\Big(\sum_{l\in Q}\big(A_l(\tau)-a_l\big)+\epsilon\Big)\Big\}. \tag{4.7}$$
--
--   This is a deterministic, sample-path statement: whatever the arrivals and whatever the policy, the total backlog dominates the worst of $2^L$ random walks with drift $\epsilon$. Combined with the strong law (4.12) it yields Theorem 4.1.
--
--   **Formalization Note.** The page sums over $\tau=0,\dots,t$ in (4.7) and (4.12), but arrivals start in slot 1 and (4.10) sums over $\tau=1,\dots,t$; the formalization sums over the $t$ arrival slots $1,\dots,t$. In Lean `A τ` is the arrival vector of slot $\tau+1$ and the sum is over `τ ∈ range t`. The minimum over $Q$ includes $Q=\emptyset$ (value $t\epsilon$). The statement does not assume $\epsilon>0$ or $a\ge0$, which the argument does not use.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1942, proof of Theorem 4.1, (4.7) (with (4.8)–(4.11), pp. 1942)

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

namespace ConstrainedQueueing.Nonstationary

/-- Display (4.7), proof of Theorem 4.1 (p. 1942), pathwise: if `ε` has the property of
Corollary 4.1 for the rate vector `a`, then along every run of every admissible history-dependent
policy, for every arrival sequence, the total number of customers at the end of slot `t` is at
least the minimum over all sets `Q` of queues of `∑_{τ=1}^{t} (∑_{l∈Q} (A_l(τ) - a_l) + ε)`.
Here `A τ` are the arrivals of slot `τ + 1`, so the sum over `τ ∈ range t` covers slots `1, …, t`. -/
theorem display_4_7 {L N : ℕ} (net : Network L N) (a : Fin L → ℝ) (ε : ℝ)
    (hε : ∀ f ∈ coS net, ∀ W : Finset (Fin L), IsMinCut net a f W →
      ∑ l ∈ W, a l - ε ≥ ∑ i ∈ serverOut net W, f i)
    (π : HistPolicy L N) (hπ : IsAdmissiblePolicy net π)
    (x0 : Fin L → ℕ) (A : ℕ → Fin L → ℕ) (X : ℕ → Fin L → ℕ) (hX : IsRun net π x0 A X) :
    ∀ t : ℕ,
      (Finset.univ : Finset (Finset (Fin L))).inf' ⟨∅, Finset.mem_univ _⟩
          (fun Q => ∑ τ ∈ Finset.range t, (∑ l ∈ Q, ((A τ l : ℝ) - a l) + ε))
        ≤ ∑ l, (X t l : ℝ) := by sorry

end ConstrainedQueueing.Nonstationary
