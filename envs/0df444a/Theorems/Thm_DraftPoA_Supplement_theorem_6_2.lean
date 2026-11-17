-- Prove2me | Theorems.Thm_DraftPoA_Supplement_theorem_6_2
-- name    : DraftPoA.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:28:18.944203+00:00
-- url     : https://prove2.me/theorems/d96f216f-efa9-45a8-a1a1-885b8b249f22
-- title:
--   Theorem 6.2 — additive efficiency under per-item no-overbidding
-- statement:
--   Fix a draft auction with $m$ items, a nonnegative bid increment $\delta$, a cap at least every singleton value, and additive bidders.
--
--   In the per-item restricted game, every pure Nash equilibrium $b$ satisfies
--
--   $$
--   \delta=0\implies \mathrm{SW}(b)=\mathrm{OPT},
--   $$
--
--   and, for $\delta>0$,
--
--   $$
--   \mathrm{SW}(b)\ge \mathrm{OPT}-2m\delta(m+1)^m.
--   $$
--
--   The same two conclusions hold for every pure Nash equilibrium of the unrestricted draft auction whose equilibrium strategies never overbid per item at any public node. In the restricted clause, both the played profile and every allowed deviation obey the marginal-value condition from Definition 6.1; in the unrestricted clause, deviations remain unrestricted.
--
--   The theorem shows that per-item overbidding is necessary for substantial inefficiency at pure Nash equilibrium when every bidder is additive.
--
--   Differences from the source:
--   - encoding: the source's standing model has a positive bidder count → Lean parametrizes it as $q+1$; reason: these are exactly the positive natural bidder counts
--   - encoding: Section 2 supplies $\delta\ge0$ and a cap at least every singleton value → Lean writes both standing assumptions as theorem hypotheses; reason: they define the source's bid grid and do not narrow its instances
--   - encoding: $\mathrm{SW}(b)\ge\mathrm{OPT}-2m\delta(m+1)^m$ → Lean writes the same inequality with the lower bound on the left; reason: this is syntactic reordering only
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Theorem 6.2 p.11 (PDF 12), proof App. D.1 pp.27–28 (PDF 28–29)

import Mathlib
import Definitions.Def_DraftPoA_Supplement_Model

namespace DraftPoA.Supplement

/-- **Theorem 6.2 (efficiency under per-item no-overbidding).**

For additive bidders, every pure Nash equilibrium of the per-item restricted game is efficient
with continuous bids and, on a positive grid, loses at most `2 m δ (m + 1)^m` welfare. The same
two conclusions hold in the unrestricted game when every equilibrium strategy obeys per-item
no-overbidding at every public node.

Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission
(manuscript sha256 270ffdaa…), Theorem 6.2, p.11 (PDF 12), proved in App. D.1, pp.27–28
(PDF 28–29).

**Formalization Note.** `IsRestrictedPureNash` restricts both played strategies and deviations;
the second clause uses the published unrestricted `IsPureNash` predicate and separately imposes
no-overbidding only on the equilibrium profile, exactly as in the theorem. The standing bid-grid
condition `δ ≥ 0` and the cap on singleton values are made explicit from Section 2. -/
theorem theorem_6_2 :
    ∀ (q m : ℕ) (δ Mbar : ℝ) (prio : Equiv.Perm (Fin (q + 1)))
      (v : Fin (q + 1) → Finset (Fin m) → ℝ),
      0 ≤ δ → DraftPoA.IsCapped v Mbar → (∀ i, DraftPoA.IsAdditive (v i)) →
      (∀ b : Fin (q + 1) → DraftPoA.Strategy (q + 1) m δ Mbar,
        IsRestrictedPureNash prio v b →
          (δ = 0 → DraftPoA.SW prio v b = DraftPoA.OPT v) ∧
          (0 < δ →
            DraftPoA.OPT v - 2 * (m : ℝ) * δ * (m + 1 : ℝ) ^ m ≤ DraftPoA.SW prio v b)) ∧
      (∀ b : Fin (q + 1) → DraftPoA.Strategy (q + 1) m δ Mbar,
        DraftPoA.IsPureNash prio v b → ProfileNoOverbid v b →
          (δ = 0 → DraftPoA.SW prio v b = DraftPoA.OPT v) ∧
          (0 < δ →
            DraftPoA.OPT v - 2 * (m : ℝ) * δ * (m + 1 : ℝ) ^ m ≤ DraftPoA.SW prio v b)) := by sorry

end DraftPoA.Supplement
