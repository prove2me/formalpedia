-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_lemma_3_1
-- name    : ConstrainedQueueing.Nonstationary.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:05.853061+00:00
-- url     : https://prove2.me/theorems/6d80349a-5ece-4700-ab38-6a80e22e4413
-- title:
--   Lemma 3.1, p. 1940 (one class, M = I) — C̄′ = {a ≥ 0 : ∃ f ∈ F_a, c ∈ co(S), f ≤ c}
-- statement:
--   Consider the single-class network with one-slot service times ($m_i=1$ for every server). For a rate vector $a\in\mathbb R^L$ let $F_a$ be the set of $a$-admissible flows, i.e. vectors $f\in\mathbb R^N$ with $f\ge0$ and $a=-Rf$, where $R$ is the routing matrix. Let $C'$ be the set of nonnegative $a$ for which some $f\in F_a$ and some $c\in\mathrm{co}(S)$ satisfy $f_i<c_i$ whenever $f_i>0$ and $f_i=0$ whenever $c_i=0$. Then the closure of $C'$ is
--   $$\bar C'=\{a\ge 0:\ \text{there exist } f\in F_a \text{ and } c\in\mathrm{co}(S) \text{ with } f\le c\}.$$
--
--   This is the specialisation of the paper's Lemma 3.1 to $J=1$ and $M=I$, the setting of §IV. It identifies the boundary of the region outside of which, by Theorem 4.1, no policy can keep the queues bounded; the proof of Lemma 4.1 uses the inclusion of the right-hand side in $\bar C'$.
--
--   **Formalization Note.** The closure is taken in `Fin L → ℝ` with its product topology. Both sides include $a\ge0$, the shared convention for rate vectors (the paper's sets carry no explicit sign condition). No hypothesis on $S$ is needed.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1940, §III.C, Lemma 3.1, specialised to one class and M = I as in §IV, p. 1941

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

namespace ConstrainedQueueing.Nonstationary

/-- Lemma 3.1 (p. 1940), for one class and `M = I` (§IV: `M_i(t) = 1`): the closure of `C'` is
the set of nonnegative rate vectors `a` for which there are an `a`-admissible flow `f` and a
point `c ∈ co(S)` with `f ≤ c`. -/
theorem lemma_3_1 {L N : ℕ} (net : Network L N) :
    closure (Cprime net) =
      {a : Fin L → ℝ | 0 ≤ a ∧ ∃ f, IsAdmissibleFlow net a f ∧ ∃ c ∈ coS net, f ≤ c} := by sorry

end ConstrainedQueueing.Nonstationary
