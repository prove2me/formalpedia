-- Prove2me | Theorems.Thm_ConservativePJ_ManyPlayers_theorem_1_2
-- name    : ConservativePJ.ManyPlayers.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:48.83721+00:00
-- url     : https://prove2.me/theorems/1ccef142-62e3-4850-883e-b73a108d2c1b
-- title:
--   Theorem 1.2 (guarantee) — one-bit selection gains $\min\{p_i,1-p_i\}/(32\sqrt{1+p_1+\dots+p_d})$ at every coordinate
-- statement:
--   **One-bit selection.** For every $d$ there is a one-bit protocol with public randomness, depending only on $d$, with the following property. Let $V,V'\in\{0,1\}^d$ be independent and identically distributed, with an arbitrary joint law of the coordinates, and let $p_i=\Pr[V_i=1]$. Then at every coordinate $i\in[d]$ the receiver succeeds with probability at least
--   $$p_i+\frac{\min\{p_i,\,1-p_i\}}{32\sqrt{1+p_1+\cdots+p_d}}.$$
--
--   The order of quantifiers matters: one protocol serves every law of $(V,V')$ and every coordinate. The result is the step that adds a player in the protocols for pointer jumping (Lemma 4.1) and that lowers the error (Lemma A.3.1). The optimality sentence of Theorem 1.2 (Theorem A.2.1) is not part of this item.
--
--   Differences from the source:
--   - generalization: "a one-bit protocol with public randomness" → the public string is uniform on a finite set `Fin R`, and the bit and the receiver's choice are deterministic functions of the string and the player's input; reason: such a protocol is a one-bit protocol with public randomness, so the Lean existential implies the printed one; App. A.1 implements the paper's selector exactly in this form
--   - encoding: V, V′ i.i.d. with an arbitrary law on {0,1}^d; coordinates [d] → a probability mass function `ν` on `Fin d → Bool`; coordinates `Fin d`; reason: every law on a finite set is given by its weights; relabelling
--   - encoding: only the first (guarantee) sentence of Theorem 1.2 → the guarantee; reason: the optimality sentence is Theorem A.2.1's content (README); the milestone is the guarantee
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), p. 4 (PDF 6), Theorem 1.2 (first assertion); proof App. A.1, pp. 16–17 (PDF 18–19)

import Mathlib
import Definitions.Def_ConservativePJ_ManyPlayers_OneBitSelection

namespace ConservativePJ.ManyPlayers

theorem theorem_1_2 (d : ℕ) :
    ∃ Q : OneBitProtocol d, ∀ ν : (Fin d → Bool) → ℝ, IsPMF ν → ∀ i : Fin d,
      marginal ν i + min (marginal ν i) (1 - marginal ν i) /
          (32 * Real.sqrt (1 + ∑ j : Fin d, marginal ν j)) ≤ Q.successAt ν i := by sorry

end ConservativePJ.ManyPlayers
