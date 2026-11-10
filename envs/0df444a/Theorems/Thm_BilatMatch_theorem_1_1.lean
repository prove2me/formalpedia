-- Prove2me | Theorems.Thm_BilatMatch_theorem_1_1
-- name    : BilatMatch.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:52.321772+00:00
-- url     : https://prove2.me/theorems/e9544f19-35c0-4fea-8bb7-dd12e0c03947
-- title:
--   Theorem 1.1 (Bilateral-to-Matching Reduction) — bilateral $V_\alpha\ge\beta\,\mathrm{FB}$ over finite priors implies $V_\alpha\ge\beta\,\mathrm{FB}$ in every matching market
-- statement:
--   Fix $\alpha,\beta\ge0$. Suppose that every bilateral trade with independent finitely supported priors $F_B,F_S$ satisfies
--   $$V_\alpha(F_B,F_S)\ \ge\ \beta\,\mathrm{FB}(F_B,F_S).$$
--   Then every matching market $\mathcal I$ with countably many buyers and sellers, any independent priors, a nonempty downward-closed family of feasible matchings, and $\mathrm{FB}(\mathcal I)<\infty$ satisfies
--   $$V_\alpha(\mathcal I)\ \ge\ \beta\,\mathrm{FB}(\mathcal I).$$
--
--   Here $V_\alpha$ is the supremum of $\mathrm{GFT}+\alpha\,\mathrm{Rev}$ over admissible, Bayesian incentive compatible and interim individually rational mechanisms, with no budget constraint. Bilateral trade is therefore the worst case for every fixed-multiplier efficiency bound; with budget duality the same transfer holds for second-best guarantees (Corollary 1.2).
--
--   **Formalization Note** Priors are arbitrary Borel probability measures on $\mathbb R$ (no sign, moment or density condition); $\mathrm{FB}$ is computed in $[0,\infty]$ and $\beta\,\mathrm{FB}$ uses its real value under $\mathrm{FB}<\infty$.
--
--   Differences from the source:
--   - encoding: a mechanism specifies a distribution over feasible matchings and a signed payment at every report profile → a feasible matching selected by a uniform seed ω ∈ [0,1], with deterministic measurable signed payments; reason: every measurable distribution over feasible matchings of a countable edge set is the law of such a selection; standard Lean representation
--   - reading: BIC/IIR for each type (general priors, p.7: V_α over admissible BIC/IIR mechanisms) → BIC and IIR at every real type and every real report; reason: the paper's mechanisms are built with whole-line BIC/IIR (eq. (1), Lemma B.4); for finite priors the support-restricted and whole-line values coincide (Lemma B.4(i)), so the hypothesis is unchanged and the conclusion takes the stronger reading
--   - encoding: V_α ≥ β FB with FB < ∞ → (β · FB.toReal : EReal) ≤ V_α, with FB < ⊤ as a hypothesis for the market (bilateral FB with finite priors is always finite); reason: FB is a [0,∞]-valued integral; toReal is exact under finiteness
--   - encoding: admissible mechanisms (footnote 1, p.5) → finite expected total absolute payments and absolute realized gains, integrable interim payment integrands; reason: makes every expectation in GFT, Rev, BIC and IIR well defined
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Theorem 1.1, p.1 (pdf p.3)

import Mathlib
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB
import Definitions.Def_BilatMatch_bilateral

open MeasureTheory

namespace BilatMatch

/-- **Theorem 1.1 (Bilateral-to-Matching Reduction).** Liu, Qin, Wang, *From Bilateral Trade to
Matching Markets: Sharp Gains from Trade*, arXiv:2609.30702 (held version, sha256 ff1490ad…),
Theorem 1.1, p.1 (pdf p.3).

Fix `α, β ≥ 0`. If `V_α ≥ β FB` for every bilateral trade with independent finitely supported priors,
then `V_α ≥ β FB` for every matching market with countably many buyers and sellers, arbitrary
independent (Borel probability) priors with `FB < ∞`, and a nonempty downward-closed family of
feasible matchings.

**Formalization Note**
* `V_α` (`Valpha`) is the `EReal` supremum of `GFT + α Rev` over admissible mechanisms (randomized
  through a uniform seed, deterministic signed payments) that are BIC and IIR at every real type and
  every real report; no budget constraint enters `V_α`. For finitely supported bilateral priors this
  equals the support-restricted value of Lemma 2.1.
* `FB` is a `lintegral` in `ℝ≥0∞`; the paper's standing assumption `FB < ∞` is the hypothesis `hfin`,
  and `β FB` is `β * (FB I).toReal`. Bilateral first best with finite priors is always finite.
* The types `B`, `S` are arbitrary countable types (finite and empty included). -/
theorem theorem_1_1 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hbil : ∀ GB GS : Measure ℝ, IsFiniteSupport GB → IsFiniteSupport GS →
      ((β * (FB (bilateral GB GS)).toReal : ℝ) : EReal) ≤ Valpha (bilateral GB GS) α)
    {B S : Type*} [Countable B] [Countable S] (I : Market B S) (hI : I.IsValid)
    (hfin : FB I < ⊤) :
    ((β * (FB I).toReal : ℝ) : EReal) ≤ Valpha I α := by sorry

end BilatMatch
