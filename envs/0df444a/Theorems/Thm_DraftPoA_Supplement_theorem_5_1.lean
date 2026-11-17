-- Prove2me | Theorems.Thm_DraftPoA_Supplement_theorem_5_1
-- name    : DraftPoA.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:27:43.789205+00:00
-- url     : https://prove2.me/theorems/e71a6731-d7c8-4bb7-8ad2-d82d122908b0
-- title:
--   Theorem 5.1 — efficient equilibrium and price of stability one
-- statement:
--   Let there be at least two bidders and $m$ items. Bidder $i$ has nonnegative additive item values $c_i(j)$, every value is an integer multiple of a bid increment $\delta>0$, and the bid cap is at least every item value.
--
--   Then the draft auction has a pure subgame-perfect equilibrium $b$ such that:
--
--   1. its allocation is efficient, so $\mathrm{SW}(b)=\mathrm{OPT}$;
--   2. every item $j$ is sold to a bidder with highest value for $j$;
--   3. if $s_j$ is the largest value for $j$ among bidders other than its winner, its sale price lies in $\{s_j,s_j+\delta\}$; and
--   4. at every public node, every prescribed bid is at most the bidder's marginal value for each item in the set she names.
--
--   Consequently, for every positive number of items and every positive grid increment, the price of stability for additive grid-valued instances is exactly $1$, where the best-equilibrium infimum is taken separately for each instance before the worst-instance supremum.
--
--   This theorem identifies the welfare loss in the paper's lower bound as a property of a bad equilibrium rather than of the draft-auction instances themselves.
--
--   Differences from the source:
--   - encoding: the source writes an arbitrary bidder count $n\ge2$ → Lean parametrizes it as $q+2$; reason: these are exactly the natural numbers at least two
--   - encoding: the source calls item values integer multiples of $\delta$ → Lean uses a natural multiplier together with nonnegativity; reason: this is the same nonnegative bid grid
--   - encoding: the source defines price of stability as the best-equilibrium ratio followed by the worst-instance ratio → Lean uses an instance-wise infimum in $[0,\infty]$ followed by a supremum, with the published $0/0=0$ convention; reason: this preserves the source's quantifier order and makes the total quotient explicit
--   - encoding: the source implicitly considers a positive item set when saying the price of stability is one → Lean requires $m>0$ only for that PoS clause while retaining the equilibrium statement at $m=0$; reason: the no-item ratio is the undefined economic case and equals $0/0$ under the total quotient
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Theorem 5.1 p.11 (PDF 12), proof App. C.1 pp.24–25 (PDF 25–26)

import Mathlib
import Definitions.Def_DraftPoA_Supplement_Model

namespace DraftPoA.Supplement

/-- **Theorem 5.1 (efficient equilibrium and price of stability one).**

Let all bidders be additive with nonnegative item values that are integer multiples of a positive
bid increment, and let there be at least two bidders. There is a pure subgame-perfect equilibrium
whose allocation is efficient, in which every item is sold to a highest-value bidder at its
second-highest value or one grid increment above, and in which no prescribed strategy overbids
the bidder's marginal value for any named item. Consequently the additive grid-valued price of
stability is one for every positive number of items.

Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission
(manuscript sha256 270ffdaa…), Theorem 5.1, p.11 (PDF 12), proved in App. C.1, pp.24–25
(PDF 25–26).

**Formalization Note.** The number of bidders is written `q + 2`, exactly parametrizing `n ≥ 2`.
`additiveGridPoS` takes the infimum over pure SPE profiles separately for each instance before
taking the supremum over instances. The positive-item hypothesis in the PoS clause excludes only
the undefined economic case with no item; the existence, allocation, price, and no-overbidding
clauses themselves cover `m = 0`. -/
theorem theorem_5_1 :
    (∀ (q m : ℕ) (δ Mbar : ℝ) (prio : Equiv.Perm (Fin (q + 2)))
      (c : Fin (q + 2) → Fin m → ℝ), 0 < δ → IsAdditiveGridData c δ Mbar →
      ∃ b : Fin (q + 2) → DraftPoA.Strategy (q + 2) m δ Mbar,
        DraftPoA.IsPureSPE prio (additiveValue c) b ∧
        DraftPoA.SW prio (additiveValue c) b = DraftPoA.OPT (additiveValue c) ∧
        ProfileNoOverbid (additiveValue c) b ∧
        ∀ j : Fin m,
          (∀ i : Fin (q + 2),
            c i j ≤ c (DraftPoA.buyer (DraftPoA.play prio b) j) j) ∧
          ∃ s : ℝ,
            (∃ e : Fin (q + 2),
              e ≠ DraftPoA.buyer (DraftPoA.play prio b) j ∧ c e j = s ∧
              ∀ i : Fin (q + 2), i ≠ DraftPoA.buyer (DraftPoA.play prio b) j → c i j ≤ s) ∧
            (DraftPoA.price (DraftPoA.play prio b) j = s ∨
              DraftPoA.price (DraftPoA.play prio b) j = s + δ)) ∧
    (∀ (m : ℕ) (δ : ℝ), 0 < m → 0 < δ → additiveGridPoS m δ = 1) := by sorry

end DraftPoA.Supplement
