-- Prove2me | Theorems.Thm_DecQueueLearning_lemma_3_5
-- name    : DecQueueLearning.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:27.178746+00:00
-- url     : https://prove2.me/theorems/cecb7aaf-712c-4853-a20c-ef7343da851c
-- title:
--   Lemma 3.5 — unmatched queues update their prices
-- statement:
--   Run the epoch auction with general nonnegative weights $w$ starting at slot $t_0$, and assume no two queues send equal bids to one server in the epoch. Fix a slot $t\ge t_0$ with $t+L_{\mathrm{check}}+1\le t_0+L_{\mathrm{conv}}-1$ and a server $j$ with $|R_j(t)|>1$. Then all but one queue of $R_j(t)$ update (leave their checking period and re-select, lines 6–10 of Algorithm 2) at least once in $[t+1,\,t+L_{\mathrm{check}}+1]$:
--   $$
--   \big|\{i\in R_j(t):\ i\text{ does not re-select in any slot of }[t+1,t+L_{\mathrm{check}}+1]\}\big|\ \le\ 1 .
--   $$
--   This is the step that makes the potential function of the convergence proof decrease.
--
--   Differences from the source:
--   - encoding: queues 𝒩 = [N], servers 𝒦 = [K], no request ⊥ → Fin N, Fin K (paper index = Lean index + 1), Option with none for ⊥; reason: Lean convention; same instances
--   - reading: log in eq. (2) (base unstated) → log₂ (Real.logb 2) in ξ, L_conv and the stated bound; reason: the proof of Lemma 3.6 (D.5, p. 42) bounds ⌈68pK/ε⌉(L_check + 1) by 91 (log N) K L_check/ε with p < log N halvings, which needs base 2
--   - reading: a lower bound δ on the nonzero rates, µᵢⱼ ∈ {0} ∪ [δ, 1] → 0 < δ < 1; reason: eq. (2) uses ln(1 − δ), undefined at δ = 1
--   - reading: Algorithm 2, line 1: pᵢⱼ(t₀) ← 0, while line 6 at t = t₀ reads pᵢⱼ(t₀ − 1) → pᵢⱼ(t₀ − 1) = 0 and τᵢ(t₀ − 1) = t₀ − 1; reason: the prices read in the first slot of the epoch are the initial ones
--   - reading: Algorithm 2, line 13: 'Price updates for some server j' → only line 8 sets τᵢ(t) ← t; line 10 leaves τᵢ unchanged; reason: after line 10 every payoff is nonpositive and the prices are frozen, so the queue stays at ⊥ whichever way τᵢ moves; same process
--   - reading: ties broken arbitrarily (footnote 2, p. 7; arg max in Algorithm 2, line 6) → every tie rule (TieRules), which may depend on the queue or server and on the slot, measurable in the bids; reason: measurability is what makes the queue lengths random variables
--   - generalization: weights wᵢⱼ = µ̃ᵢⱼ Qᵢ(t₀) of an epoch of the process, started at t₀ = (ℓ − 1)L_epoch + 1 → any nonnegative weights w, any start t₀ ≥ 1, any perturbations ηᵢ ∈ (0, 10⁻⁹), any service-coin path S; reason: p. 13: the results of §3.3 'hold for general wᵢⱼ'; the epoch of DAM.K is the instance w = µQ(t₀) (proved by rfl in the sanity file)
--   - reading: ties are broken arbitrarily and a.s. do not exist (footnote 2, p. 7) → hypothesis NoBidTies: no two queues send equal bids to one server in a slot of the epoch; reason: with an exact tie a slot-dependent tie rule can serve two tied queues alternately, so neither updates and the system never converges
--   - reading: update one of their prices → re-select: line 8 (raise a price) or line 10 (stop requesting, p_{i,⊥} ← 0) runs; reason: with line 8 only the lemma fails: a queue whose payoff became nonpositive at every server after its last raise stops requesting without a price update, while the selected queue keeps being served
--   - reading: a time slot t → t₀ ≤ t and t + L_check + 1 ≤ t₀ + L_conv − 1; reason: in the commit phase nobody updates; two queues sharing a server at t₀ + L_conv − 1 would falsify the unrestricted statement
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Lemma 3.5, p.14 (PDF 15)

import Mathlib
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction

namespace DecQueueLearning

/-- **Lemma 3.5** (unmatched queues increase their prices), Freund–Lykouris–Weng,
arXiv:2206.03324v3, p. 14: "Fix a time slot t and a server j. If |R_j(t)| > 1, then all but one
queue in R_j(t) will update one of their prices at least once in [t + 1, t + L_check + 1]."

Stated pathwise for the epoch auction `epochRun` with general nonnegative weights: at most one
queue of `R_j(t)` does not re-select (run lines 6–10 of Algorithm 2) in a slot of
`[t + 1, t + L_check + 1]`.

**Formalization Note** (1) "Update one of their prices" is read as leaving the checking period and
re-selecting (line 8, a price update, or line 10, which sets `p_{i,⊥} ← 0` and stops requesting).
With line 8 only the statement fails: a queue whose payoff at `j` became nonpositive after its last
increment, and is non-positive everywhere, stops requesting without a price update while the
selected queue keeps being served. (2) The window lies in the converge phase,
`t₀ ≤ t` and `t + L_check + 1 ≤ t₀ + L_conv − 1` (in the commit phase nobody updates).
(3) No two queues bid equally at a server in the epoch (footnote 2, p. 7: ties a.s. do not
exist); at an exact tie a time-dependent tie rule can alternate between two tied queues and serve
both, so neither updates. -/
theorem lemma_3_5 {N K : ℕ} [NeZero N] [NeZero K] (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (rules : TieRules N K) (w : Fin N → Fin K → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (η : Fin N → ℝ) (hη : ∀ i, η i ∈ Set.Ioo (0 : ℝ) (1 / 10 ^ 9))
    (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) (ht0 : 1 ≤ t0)
    (hnt : NoBidTies ε δ (epochRun ε δ rules w η S t0) t0)
    (t : ℕ) (ht0t : t0 ≤ t) (hwin : t + Lcheck N K ε δ + 1 ≤ t0 + Lconv N K ε δ - 1)
    (j : Fin K) (hR : 1 < (R (epochRun ε δ rules w η S t0) t0 j t).card) :
    ((R (epochRun ε δ rules w η S t0) t0 j t).filter fun i =>
        ∀ t', t + 1 ≤ t' → t' ≤ t + Lcheck N K ε δ + 1 →
          (stateAt (epochRun ε δ rules w η S t0) t0 t' i).reselect = false).card ≤ 1 := by sorry

end DecQueueLearning
