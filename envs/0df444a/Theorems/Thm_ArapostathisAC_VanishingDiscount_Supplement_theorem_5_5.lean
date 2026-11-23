-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_5
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:08:36.312565+00:00
-- url     : https://prove2.me/theorems/9b64ce16-20a8-4102-b187-306179e2668c
-- title:
--   Theorem 5.5 — Assumption 5.2 (uniformly bounded mean hitting times) is equivalent to Assumption 5.6 (uniformly bounded ACOE solutions for every bounded cost and action collection)
-- statement:
--   For the transition law of the countable-state model of §5, the following are equivalent:
--
--   1. (Assumption 5.2) there is $K>0$ such that every $f\in\Pi_{SD}$ has a state $j(f)$ with $E^f_i[\tau_{\{j(f)\}}]<K$ for all $i\in S$;
--   2. (Assumption 5.6) there is $K>0$ such that, for every bounded measurable cost $c:S\times A\to\mathbb R$ and every collection of nonempty compact admissible sets $U(i)$ on which $c(i,\cdot)$ is continuous, the ACOE
--   $$\rho+h(i)=\min_{a\in U(i)}\Big\{c(i,a)+\sum_jP(j\mid i,a)h(j)\Big\}$$
--   has a bounded solution $(\rho,h)$ with $\|h\|\le K\|c\|$ (sup norms).
--
--   Thus a bounded solution of the ACOE for all bounded costs, with a uniform constant, forces a strong uniform recurrence structure.
--
--   **Formalization Note** The cost in Assumption 5.6 is signed and is a separate argument; the transition law is that of the given model, and the collections $U(i)$ range over nonempty compact subsets of the model's admissible sets. The ACOE requires summable series and an attained minimum.
--
--   Differences from the source:
--   - reading: every collection {U(i) : i ∈ S}, U(i) ⊂ A → every collection of nonempty compact U(i) ⊆ U_M(i), the admissible sets of the given model; reason: P is specified on the model's admissible pairs and Assumption 5.2 refers to the model's Π_SD; when U_M(i) = A this is the printed quantifier
--   - reading: each bounded and measurable c : S × A → ℝ → each bounded measurable signed c with c(i, ·) continuous on U(i); reason: the §5 standing convention (p. 299) that c(i, ·) is continuous applies to every model of the family
--   - encoding: ‖h‖ ≤ K‖c‖ with ‖·‖ the sup norm → |h(i)| ≤ K · sup_{(i,a) ∈ S × A} |c(i, a)| for every i, with h bounded; reason: Lean convention; c is bounded so the real supremum is the sup norm
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 303, Theorem 5.5 and Assumption 5.6; p. 302, Assumption 5.2

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Recurrence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.5 (p. 303). Assumptions 5.2 and 5.6 are equivalent: uniformly bounded mean hitting
times of some state under every `f ∈ Π_SD` hold iff there is one `K > 0` such that, for every
bounded measurable signed cost `c` and every collection of nonempty compact `U(i) ⊆ U_M(i)` on
which `c(i, ·)` is continuous, the ACOE has a bounded solution with `‖h‖ ≤ K‖c‖`. -/
theorem theorem_5_5 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) : Assumption52 M ↔ Assumption56 M := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
