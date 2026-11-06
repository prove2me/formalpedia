-- Prove2me | Theorems.Thm_AdvMultiplayer_proposition_23
-- name    : AdvMultiplayer.proposition_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:17:32.923992+00:00
-- url     : https://prove2.me/theorems/8270c01c-70f6-4de3-a351-431d4be95863
-- title:
--   Proposition 23 — computation and storage
-- statement:
--   On the construction branch: (i) preprocessing uses $O(T^{9/2}/(m^{3/2}\sqrt K(\log N)^2))$ operations and memory cells; (ii) after preprocessing, the total work of all players over the $T$ rounds is $\tilde O(T^3)$ operations, and together they use at most $O(T^2/\log N)$ cells of private memory at any time. These bounds hold even if a player accepts an incorrect row index or message.
--
--   Differences from the source:
--   - reading: O and Õ → an absolute C, and Õ(f) as C f (log N)^c with c absolute; reason: “Õ suppresses factors polynomial in log N”, p.48
--   - reading: exact arithmetic operations → ticks of the programs, with the floor as a ticked search; reason: Section 8 does not list the floor; not charging it would be the weaker reading, and the bounds survive
--   - encoding: even if a player accepts an incorrect row index or message → for every table, reward matrix and tape of the actual execution; reason: this covers every wrong acceptance
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Proposition 23, p.48

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

namespace AdvMultiplayer

/-- **Proposition 23 (computation and storage).** Gan, arXiv:2610.05688, Proposition 23, p.48. On the
construction branch: (i) preprocessing uses `O(T^{9/2}/(m^{3/2} √K (log N)²))` operations and memory cells;
(ii) after preprocessing, the total work of all players over the `T` rounds is `Õ(T³)`, and together they
use `O(T²/log N)` cells of private memory at any time. These bounds hold even if a player accepts an
incorrect row index or message.

**Formalization Note.** Operations are ticks of `sampleTable` and of the actual execution; `O(·)` is an
absolute constant quantified first, and `Õ` suppresses `(log N)^c` with `c` absolute (p.48). The last
sentence is the quantification over every table, reward matrix and tape of the actual execution. The floor
is not a unit-cost operation here (`floorProg`), and the bound survives. -/
theorem proposition_23 : ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ (p : Size) (_ : p.branch),
    (∀ ω : TableTape p, (sampleTicks p ω : ℝ) ≤
      C * ((p.T : ℝ) ^ ((9 : ℝ) / 2) /
        ((p.m : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (p.K : ℝ) * Real.log (p.N : ℝ) ^ 2))) ∧
    ((tableCells p : ℝ) ≤
      C * ((p.T : ℝ) ^ ((9 : ℝ) / 2) /
        ((p.m : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (p.K : ℝ) * Real.log (p.N : ℝ) ^ 2))) ∧
    (∀ (d : TableData p) (r : Rewards p) (ω : Tapes p),
      (execTicks p d RunKind.actual r ω : ℝ) ≤ C * (p.T : ℝ) ^ 3 * Real.log (p.N : ℝ) ^ c) ∧
    ∀ (d : TableData p) (r : Rewards p) (ω : Tapes p), ∀ t ∈ Finset.Icc 1 p.T,
      ((∑ i, privateCells p i ((roundAt p d RunKind.actual r ω t).post i) : ℕ) : ℝ) ≤
        C * (p.T : ℝ) ^ 2 / Real.log (p.N : ℝ) := by sorry

end AdvMultiplayer
