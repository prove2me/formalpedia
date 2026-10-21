-- Prove2me | Theorems.Thm_DelayDep_Equiv_pathwise_coupling
-- name    : DelayDep.Equiv.pathwise_coupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:07.127415+00:00
-- url     : https://prove2.me/theorems/2de337ae-1300-4809-8c90-5d465f13949a
-- title:
--   Proof of Theorem 1, p. 3349 — same outcome for every customer at its offered wait gives the same offered waits and the same path X
-- statement:
--   This is a deterministic statement about two sample paths. Fix $n \ge 1$, interarrival times $\alpha$ and initial residual service times $u$. Consider two systems driven by the same $\alpha$ and $u$, with patience times $T_i$, $T'_i$ and virtual service-time maps $S_i(\cdot)$, $S'_i(\cdot)$. Let $w_i$ be the offered wait of customer $i$ in the first system. Suppose that for every customer $i$:
--
--   1. $w_i \le T_i$ if and only if $w_i \le T'_i$ (served in one system iff served in the other);
--   2. if $w_i \le T_i$, then $S'_i(w_i) = S_i(w_i)$ (same service time when served);
--   3. if $w_i > T_i$, then $T'_i = T_i$ (same patience when abandoning).
--
--   Then the offered-wait vectors of (2) coincide, $Z'_i = Z_i$ for every $i$, and the two state processes coincide path by path:
--   $$X'(\tau) = X(\tau) \quad \text{for every } \tau \ge 0.$$
--
--   In the proof of Theorem 1 this is the step showing that the coupled system has exactly the dynamics of the endogenous system it was built from.
--
--   **Formalization Note** Customers are 0-based. Hypotheses use the tie convention of (2) (served iff wait $\le$ patience), whereas steps (ii)–(iii) of the paper split on $t \le z$; the two differ only on null events.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3349 (PDF 6), proof of Theorem 1, paragraph "Steps (i)–(iii) above guarantee …"

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

/-- Proof of Theorem 1, p. 3349 (deterministic): two systems driven by the same interarrival times
`α` and initial residual service times `u`, in which every customer has the same outcome at the
offered wait `w i` of the first system — served in both (with the same service time) or abandoning
in both (with the same patience) — have the same offered-wait vectors `Z_i` for every `i` and the
same state `X(τ)` at every time `τ`. -/
theorem pathwise_coupling {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ)
    (tp tp' : ℕ → ℝ) (sv sv' : ℕ → ℝ → ℝ)
    (h_served : ∀ i, wait α u tp sv i ≤ tp i ↔ wait α u tp sv i ≤ tp' i)
    (h_service : ∀ i, wait α u tp sv i ≤ tp i →
      sv' i (wait α u tp sv i) = sv i (wait α u tp sv i))
    (h_abandon : ∀ i, ¬ wait α u tp sv i ≤ tp i → tp' i = tp i) :
    (∀ i, Zvec α u tp' sv' i = Zvec α u tp sv i) ∧
      ∀ τ : NNReal, pathX α u tp' sv' τ = pathX α u tp sv τ := by sorry

end DelayDep.Equiv
