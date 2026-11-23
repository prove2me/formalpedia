-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_4
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:07:56.52704+00:00
-- url     : https://prove2.me/theorems/c66359b9-8636-4d56-b355-ce328eb6a746
-- title:
--   Theorem 5.4 (corrected: Assumption 5.3 read with $n$-step probabilities) — Assumptions 5.1–5.3 are equivalent, and under aperiodicity Assumptions 5.1–5.5 are equivalent
-- statement:
--   In the countable-state model of §5, the following recurrence conditions on the chains of all $f\in\Pi_{SD}$ are compared:
--
--   - **5.1**: a finite $B\subset S$ and $K>0$ with $E^f_i[\tau_B]<K$ for all $i$ and $f$, and no two disjoint invariant sets;
--   - **5.2**: $K>0$ and, for each $f$, a state $j(f)$ with $E^f_i[\tau_{\{j(f)\}}]<K$ for all $i$;
--   - **5.3** (simultaneous Doeblin): a finite $B$, $n\ge1$ and $\alpha>0$ with $\sum_{j\in B}P^n(f)(i,j)\ge\alpha$ for all $i$, $f$, and no two disjoint invariant sets;
--   - **5.4** (scrambling): $n\ge1$, $\alpha>0$ with $\sum_j\min\{P^n_{i_1j}(f),P^n_{i_2j}(f)\}\ge\alpha$ for all $f,i_1,i_2$;
--   - **5.5** (ergodicity): $n\ge1$, $\rho>0$ and $\eta(f)\in\mathcal P(S)$ with $\sum_j|P^m_{ij}(f)-\eta(f)(j)|\le2(1-\rho)^{\lfloor m/n\rfloor}$ for all $i$, $m\ge1$,
--
--   where $\tau_B=\min\{t\ge1:X_t\in B\}$. Then 5.1, 5.2 and 5.3 are equivalent; if moreover the chain of every $f\in\Pi_{SD}$ is aperiodic, all five are equivalent.
--
--   Each of these conditions yields a bounded solution of the ACOE (Remark 5.4), so the theorem shows that several uniform recurrence notions used in the literature coincide.
--
--   **Formalization Note** An invariant set is a nonempty $C$ with $P(C\mid i,f(i))=1$ for $i\in C$; aperiodicity means that every recurrent state has period one. Hitting-time expectations are in $[0,\infty]$.
--
--   Differences from the source:
--   - correction: Assumption 5.3 introduces an integer n ≥ 1 but its display reads ∑_{j ∈ A} P(j | i, f(i)) ≥ α (pp. 302–303) → ∑_{j ∈ B} Pⁿ(f)(i, j) ≥ α with the n-step probabilities; reason: n is otherwise unused and the neighbouring Assumptions 5.4–5.5 use n-step matrices; with the one-step display 5.1 ⇒ 5.3 fails: on S = {0} ∪ {(k, 1), (k, 2)}, 0 → (k, 1) with probability 2^{−k}, (k, 1) → (k, 2) → 0, every E τ_{{0}} ≤ 3 but no finite set receives one-step mass from all (k, 1)
--   - reading: an invariant set → a nonempty set C with P(C | i, f(i)) = 1 for every i ∈ C; reason: the usual meaning (closed set); the empty set must be excluded for the condition to say anything
--   - reading: the corresponding process is aperiodic → every recurrent state has period one; reason: periodicity of transient states does not affect 5.4–5.5; this is the weakest reading of the hypothesis
--   - encoding: E^f_i[τ_B] as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 303, Theorem 5.4; pp. 302–303, Assumptions 5.1–5.5 and (5.11)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Recurrence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.4 (p. 303). Assumptions 5.1–5.3 are equivalent. Also, if for every `f ∈ Π_SD` the
corresponding process is aperiodic, then Assumptions 5.1–5.5 are equivalent. Assumption 5.3 is
read with the `n`-step transition probabilities `Pⁿ(f)(i, j)`. -/
theorem theorem_5_4 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) :
    (Assumption51 M ↔ Assumption52 M) ∧ (Assumption52 M ↔ Assumption53 M) ∧
    ((∀ f : StationaryPolicy M, IsAperiodic M f) →
      (Assumption51 M ↔ Assumption54 M) ∧ (Assumption51 M ↔ Assumption55 M)) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
