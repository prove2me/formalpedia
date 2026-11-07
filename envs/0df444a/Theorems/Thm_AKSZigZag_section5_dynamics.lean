-- Prove2me | Theorems.Thm_AKSZigZag_section5_dynamics
-- name    : AKSZigZag.section5_dynamics
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:56.98846+00:00
-- url     : https://prove2.me/theorems/4090fd39-e0f6-4c91-8a09-7e8b2f835e17
-- title:
--   §5 Dynamics, p.6 — no register moves up, none moves down more than two levels (corrected: parenthetical dropped)
-- statement:
--   Let $A>2$ and $n$ be powers of $2$ and $0\le t<\log_2 n$. Suppose a register is assigned to a node on level $i$ at time $t$ and to a node on level $i'$ at time $t+1$. Then
--   $$
--   i\le i'\le i+2 .
--   $$
--   So, when time increases from $t$ to $t+1$, no register moves up the tree and none moves down more than two levels.
--
--   Lemma 1 uses these facts to compare the errors before and after the reassignment.
--
--   Differences from the source:
--   - correction: A > 2 ensures that no register moves down more than two levels (Yt+1(i+3) > Yt(i+1)) → the movement claim only; the parenthetical inequality is not stated; reason: the parenthetical is false when both sides are 0: n = 1024, A = 16, t = 3, i = 0 gives X₃(1) = ⌊1024·2⁻³·16⁻²/32⌋ = 0; the movement claims it supports hold
--   - reading: about 1/A proportion of some intervals remain unchanged, most registers move down one or two levels (about half-half) → not stated; reason: the approximate proportions are informal; the two exact claims of the passage are stated
--   - generalization: A > 10 (§5 standing assumption), t ≥ 1 → A > 2, and t = 0 included; reason: the sentence itself says A > 2 suffices; t = 0 (all registers on the root) is the first reassignment of the algorithm
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §5 (Dynamics), p.6

import Mathlib
import Definitions.Def_AKSZigZag_RegisterAssignment

namespace AKSZigZag

/-- **Dynamics of the register assignment** (AKS, STOC 1983, doi:10.1145/800061.808726, §5,
p.6): "As time increases from t to t+1, we reassign the registers to nodes. … No register moves
up, and A > 2 ensures that no register moves down more than two levels."

Let `A > 2` and `n` be powers of 2 and `0 ≤ t < log₂ n`. If a register is assigned to a node on
level `i` at time `t` and to a node on level `i'` at time `t + 1`, then `i ≤ i' ≤ i + 2`.

**Formalization Note.** The parenthetical justification "(Y_{t+1}(i+3) > Y_t(i+1))" is not
stated: it fails when both sides are `0` (`n = 1024`, `A = 16`, `t = 3`, `i = 0`). The claims it
supports are stated. The case `t = 0` (everything on the root) is included. -/
theorem section5_dynamics (A n t : ℕ) (hA : 2 < A) (hApow : ∃ k, A = 2 ^ k)
    (hn : ∃ k, n = 2 ^ k) (ht : t + 1 ≤ Nat.log 2 n) (r : Fin n) (i j i' j' : ℕ)
    (h₁ : r ∈ nodeRegs A n t i j) (h₂ : r ∈ nodeRegs A n (t + 1) i' j') :
    i ≤ i' ∧ i' ≤ i + 2 := by sorry

end AKSZigZag
