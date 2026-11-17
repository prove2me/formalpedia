-- Prove2me | Theorems.Thm_DraftPoA_Supplement_theorem_6_3
-- name    : DraftPoA.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:28:54.433803+00:00
-- url     : https://prove2.me/theorems/0997deb8-237d-421f-b165-f547f52c8c0f
-- title:
--   Theorem 6.3 — unit-demand lower bound under per-item no-overbidding
-- statement:
--   Write $H_N$ for the $N$-th harmonic number, $K=\lceil H_N\rceil$, $\delta_N=1/(4N^2K^2)$, $w=1/(2NK)$, and $r=\lceil(\ln K+3)/w\rceil$.
--
--   There is an absolute constant $C>0$ such that, for every $N\ge4$, the Appendix D.2 instance has exactly
--
--   $$
--   m_N=N+2r+1\le C N\ln N\ln\ln N
--   $$
--
--   items: $N$ sink items, two rent blocks of $r$ items, and one private item. Its bidders are additive except for the unit-demand punisher, ties use the priority order $A\succ P\succ W\succ C_1\succ C'_1\succ\cdots$, and bids lie on the grid of increment $\delta_N$. The per-item restricted game has a behavior-strategy subgame-perfect equilibrium $b$ that is pure at every node on its realized path and satisfies
--
--   $$
--   \frac{\mathrm{OPT}}{\mathrm{SW}(b)}\ge
--   \frac{H_N}{2\ln(H_N+1)+10}.
--   $$
--
--   The welfare is positive. At damaged off-path subgames the behavior equilibrium may mix, as in the paper's backward-induction completion. Adding any number of dummy items preserves the valuation classes, the restricted behavior SPE, purity along the path, and the same finite-$N$ ratio.
--
--   Consequently, there are $C'>0$ and $m_0$ such that for every $m\ge m_0$, if $N$ is the largest construction size with $m_N\le m$, then the per-item restricted behavior-SPE price of anarchy at increment $\delta_N$ obeys
--
--   $$
--   \mathrm{PoA}_{\mathrm{restricted}}(m,\delta_N)\ge
--   \left(\frac12-\frac{C'}{\ln\ln m}\right)\frac{\ln m}{\ln\ln m}.
--   $$
--
--   This is the paper's $(1/2-o(1))\ln m/\ln\ln m$ lower bound and shows that unit-demand bidders restore logarithmic inefficiency even when every action and deviation satisfies per-item no-overbidding.
--
--   Differences from the source:
--   - reading: the theorem says there is an instance with $N$ sink items and $m=O(N\ln N\ln\ln N)$ → Lean uses the exact Appendix D.2 family with $m_N=N+2r+1$, its named bidders, values, and priority order; reason: the proof defines this instance and the exact size is needed for the consequence
--   - encoding: a behavior strategy is a distribution over legal actions at every public node → Lean uses node-indexed probability mass functions and recursively sums the independent action draws over the finite game tree; reason: $\delta_N>0$ makes every action set and the horizon finite, so this represents every source behavior strategy
--   - encoding: the equilibrium is pure along its path → Lean requires point-mass action distributions at every nonterminal prefix of a pure profile's realized path; reason: this is the literal public-node meaning and leaves damaged off-path subgames free to mix
--   - encoding: $\mathrm{OPT}/\mathrm{SW}(b)\ge R$ → Lean requires $\mathrm{SW}(b)>0$ and writes $R\,\mathrm{SW}(b)\le\mathrm{OPT}$; reason: this is equivalent and avoids total real division at zero
--   - encoding: the proof's dummy-item paragraph for other item counts → Lean states the explicit family after every number of dummy items; reason: this is the construction used by the theorem's final all-large-$m$ conclusion
--   - generalization: the source states the consequence as $(1/2-o(1))\ln m/\ln\ln m$ → Lean states the proof's quantitative form $(1/2-C/\ln\ln m)\ln m/\ln\ln m$ after one threshold; reason: the explicit size formula and harmonic estimates in the paper give this rate, which implies the printed $o(1)$ statement
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Theorem 6.3 p.12 (PDF 13), proof App. D.2 pp.28–32 (PDF 29–33)

import Mathlib
import Definitions.Def_DraftPoA_Supplement_Model

namespace DraftPoA.Supplement

/-- **Theorem 6.3 (unit-demand lower bound under per-item no-overbidding).**

There is one absolute size constant such that, for every `N ≥ 4`, the explicit Appendix D.2
instance has `N + 2r + 1 = O(N log N log log N)` items, additive or unit-demand bidders, the
priority order `A ≻ P ≻ W ≻ C₁ ≻ C₁' ≻ ⋯`, and bid increment
`1 / (4 N² ⌈H_N⌉²)`. Its per-item restricted game has a behavior-strategy subgame-perfect
equilibrium that is pure along its realized path and whose welfare ratio is at least
`H_N / (2 log (H_N + 1) + 10)`. The construction remains valid after adding dummy items, and
therefore gives the quantitative `(1/2 - o(1)) log m / log log m` lower bound for every
sufficiently large item count.

Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission
(manuscript sha256 270ffdaa…), Theorem 6.3, p.12 (PDF 13), App. D.2, pp.28–32
(PDF 29–33).

**Formalization Note.** The source's `m = O(N log N log log N)` is represented by one positive
constant quantified before `N`, while the actual constructed size is fixed as `supplementItemCount
N = N + 2 * rOf N + 1`. The final `o(1)` is a positive constant and threshold quantified before
`m`; `N` is required to be the largest unpadded construction fitting in `m`. The middle clause is
the dummy-item padding paragraph on p.32. `IsRestrictedBehaviorSPE` is a genuine behavior SPE
and restricts every deviation; `PureAlongPath` permits mixing only away from the realized path,
including at the damaged subgames used by the paper. The ratio is multiplied out and the
equilibrium welfare is required positive, avoiding division by zero. -/
theorem theorem_6_3 :
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      (supplementItemCount N : ℝ) ≤
          C * N * Real.log N * Real.log (Real.log N) ∧
      (∀ i, IsAdditiveOrUnitDemand (supplementValuation N 0 i)) ∧
      DraftPoA.IsCapped (supplementValuation N 0) 1 ∧
      ∃ b : Fin (supplementBidderCount N) →
          BehaviorStrategy (supplementBidderCount N) (supplementItemCount N)
            (DraftPoA.deltaOf N) 1,
        IsRestrictedBehaviorSPE (supplementPriority N) (supplementValuation N 0) b ∧
        PureAlongPath (supplementPriority N) b ∧
        0 < behaviorSW (supplementPriority N) (supplementValuation N 0) b ∧
        (harmonic N : ℝ) / (2 * Real.log ((harmonic N : ℝ) + 1) + 10) *
            behaviorSW (supplementPriority N) (supplementValuation N 0) b ≤
          DraftPoA.OPT (supplementValuation N 0)) ∧
    (∀ N : ℕ, 4 ≤ N → ∀ d : ℕ,
      (∀ i, IsAdditiveOrUnitDemand (supplementValuation N d i)) ∧
      DraftPoA.IsCapped (supplementValuation N d) 1 ∧
      ∃ b : Fin (supplementBidderCount N) →
          BehaviorStrategy (supplementBidderCount N) (supplementItemCount N + d)
            (DraftPoA.deltaOf N) 1,
        IsRestrictedBehaviorSPE (supplementPriority N) (supplementValuation N d) b ∧
        PureAlongPath (supplementPriority N) b ∧
        0 < behaviorSW (supplementPriority N) (supplementValuation N d) b ∧
        (harmonic N : ℝ) / (2 * Real.log ((harmonic N : ℝ) + 1) + 10) *
            behaviorSW (supplementPriority N) (supplementValuation N d) b ≤
          DraftPoA.OPT (supplementValuation N d)) ∧
    (∃ (C : ℝ) (m₀ : ℕ), 0 < C ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ N : ℕ, IsGreatest {k : ℕ | 4 ≤ k ∧ supplementItemCount k ≤ m} N ∧
        ENNReal.ofReal
            ((1 / 2 - C / Real.log (Real.log m)) *
              (Real.log m / Real.log (Real.log m))) ≤
          restrictedBehaviorPoA m (DraftPoA.deltaOf N)) := by sorry

end DraftPoA.Supplement
