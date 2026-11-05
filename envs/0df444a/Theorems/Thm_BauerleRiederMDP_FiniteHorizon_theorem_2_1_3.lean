-- Prove2me | Theorems.Thm_BauerleRiederMDP_FiniteHorizon_theorem_2_1_3
-- name    : BauerleRiederMDP.FiniteHorizon.theorem_2_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:53.737188+00:00
-- url     : https://prove2.me/theorems/8cc5de2f-cd1a-4552-a83f-6d932abce7ba
-- title:
--   Theorem 2.1.3 — a Markov Decision Model is equivalently described by disturbances and a transition function
-- statement:
--   A Markov Decision Model $(E,A,D_n,Q_n,r_n,g_N)$ is equivalently described by data $(E,A,D_n,Z,T_n,Q^Z_n,r_n,g_N)$, where $Z$ is a measurable disturbance space, $Q^Z_n(\cdot\mid x,a)$ is a stochastic kernel on $Z$ and $T_n$ is a measurable transition function. Precisely:
--
--   1. every Markov Decision Model is represented by disturbance data, with a disturbance space $Z$ of the same size as $E$;
--   2. all disturbance data represent a Markov Decision Model,
--
--   where representing means that $D_n$, $r_n$, $g_N$ agree and
--
--   $$Q_n(B\mid x,a)=Q^Z_n\big(\{z\in Z\mid T_n(x,a,z)\in B\}\,\big|\,x,a\big).$$
--
--   Most models of the book are specified through a transition function, and this result lets the general theory apply to them.
--
--   **Formalization Note.** In part 1 the space $Z$ lies in the universe of $E$, so that $Z=E$ is available. In part 2 the universe of $Z$ is arbitrary.
--
--   Differences from the source:
--   - reading: "is equivalently described by" → both directions of the relation Represents; reason: the book's proof gives exactly these two constructions, Z := E, T_n(x,a,z) := z, and the formula for Q_n
--   - encoding: Q_n, Q^Z_n, T_n and r_n are defined on D_n → they are defined on E × A; reason: D_n is measurable, so every book model extends, and Represents only compares values on D_n
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.1.3, p.15

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_DisturbanceModel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Represents

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u v w

/-- Theorem 2.1.3 (Bäuerle & Rieder (2011), p.15, PDF 30). A Markov Decision Model is equivalently
described by the data `(E, A, D_n, Z, T_n, Q^Z_n, r_n, g_N)`: every Markov Decision Model is
represented by some disturbance data, and all disturbance data represent a Markov Decision Model.

**Formalization Note.** "Equivalently described" is made precise by the book's proof: the
relation is `Represents`. In the first direction `Z` lives in the universe of `E`, so that the
book's choice `Z := E` is available. In the second direction `Z` is arbitrary. -/
theorem theorem_2_1_3 {E : Type u} {A : Type v} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ} :
    (∀ M : MarkovDecisionModel E A N, ∃ (Z : Type u) (_ : MeasurableSpace Z)
      (DM : DisturbanceModel E A Z N), Represents DM M) ∧
    (∀ (Z : Type w) [MeasurableSpace Z] (DM : DisturbanceModel E A Z N),
      ∃ M : MarkovDecisionModel E A N, Represents DM M) := by sorry

end BauerleRiederMDP.FiniteHorizon
