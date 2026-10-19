-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_proposition_3
-- name    : AddictivePlatforms.Compete.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:23.045668+00:00
-- url     : https://prove2.me/theorems/79379717-3887-4168-a247-aafd6d0bc681
-- title:
--   Proposition 3, p. 12 — scarce attention (Ā ≤ A(0)): duopolists more addictive, consumer strictly prefers monopoly; Ā ≥ Ā^M: duopolists weakly less addictive, consumer weakly prefers duopoly
-- statement:
--   Assume Assumptions 1–2 (with the mission's standing pins), and compare a monopoly ($K = 1$) with a duopoly ($K = 2$) facing the same consumer: the same utility $u$, attention cost $C$ and attention cap $\overline{A}$. Let $A(0)$ be the consumer's unconstrained attention on one platform of zero addictiveness, and $\overline{A}^M$ the least cap from which on the consumer's payoff in every monopoly equilibrium is zero.
--   1. If attention is scarce, $0 < \overline{A} \le A(0)$, then for every monopoly equilibrium with addictiveness $d^M$ and every duopoly equilibrium with addictiveness $(d_1, d_2)$,
--   $$d^M < d_1, \qquad d^M < d_2, \qquad CS^{\mathrm{duo}} < CS^{\mathrm{mono}}:$$
--   both duopolists are strictly more addictive than the monopolist and the consumer is strictly better off under monopoly.
--   2. If attention is abundant, $\overline{A} \ge \overline{A}^M$, then for every such pair of equilibria
--   $$d_1 \le d^M, \qquad d_2 \le d^M, \qquad CS^{\mathrm{mono}} \le CS^{\mathrm{duo}}:$$
--   the duopolists are (weakly) less addictive and the consumer is weakly better off under duopoly.
--
--   Here $CS$ is the consumer's payoff in the equilibrium outcome, and a monopoly equilibrium is one in which the platform breaks ties in favour of the consumer. This is the paper's headline: when attention is scarce, competition for attention lowers service quality and hurts the consumer.
--
--   **Formalization Note.** "Higher" in part 1 is stated strictly, which is what the paper's proof gives ($d^M = 0 < d^*$); "lower" in part 2 is weak, as it must be: with linear $C$ and a large cap the duopoly and monopoly addictiveness coincide (footnote 11). The addictiveness comparison of part 2 is in the proposition but not argued in the printed proof. $\overline{A} > 0$ in part 1 is a disclosed pin (at $\overline{A} = 0$ every duopoly profile is an equilibrium). Equilibria exist by Propositions 1 and 2. The existence pin is assumed for two platforms (it implies the one-platform case), and $A(d)$ is a parameter characterized by its maximizing property.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 12, Proposition 3 and its proof

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Proposition 3 (p. 12). (i) If `0 < Ā ≤ A(0)`, then in every monopoly equilibrium and every
duopoly equilibrium both duopolists choose strictly higher addictiveness than the monopolist, and the
consumer is strictly better off under monopoly. (ii) If `Ā ≥ Ā^M`, then both duopolists choose
(weakly) lower addictiveness than the monopolist, and the consumer is weakly better off under
duopoly. -/
theorem proposition_3 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Aopt : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C 2) (hA : IsUncChoice u C Aopt) :
    (∀ Abar : ℝ≥0∞, 0 < Abar → Abar ≤ ENNReal.ofReal (Aopt 0) →
      ∀ (dM : Fin 1 → ℝ) (σM : ConsumerStrategy 1), IsMonopolyEq u C Abar dM σM →
      ∀ (d : Fin 2 → ℝ) (σ : ConsumerStrategy 2), IsSPE u C Abar d σ →
        (∀ k, dM 0 < d k) ∧ consumerSurplus u C d σ < consumerSurplus u C dM σM) ∧
    (∀ Abar : ℝ≥0∞, AbarM u C ≤ Abar →
      ∀ (dM : Fin 1 → ℝ) (σM : ConsumerStrategy 1), IsMonopolyEq u C Abar dM σM →
      ∀ (d : Fin 2 → ℝ) (σ : ConsumerStrategy 2), IsSPE u C Abar d σ →
        (∀ k, d k ≤ dM 0) ∧ consumerSurplus u C dM σM ≤ consumerSurplus u C d σ) := by sorry

end AddictivePlatforms.Compete
