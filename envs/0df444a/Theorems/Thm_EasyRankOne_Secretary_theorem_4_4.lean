-- Prove2me | Theorems.Thm_EasyRankOne_Secretary_theorem_4_4
-- name    : EasyRankOne.Secretary.theorem_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:06:28.611092+00:00
-- url     : https://prove2.me/theorems/0be47fba-339b-4ab4-b808-5610e80c5b2e
-- title:
--   Theorem 4.4 — continuous-time realization: a family is realizable by an ordinal algorithm iff capacity (8) and consistency (9), realized by rule (10)
-- statement:
--   Let $M=(V,\mathcal I)$ be a matroid of positive rank on a finite ground set with a fixed label order, known to the algorithm. Let $(\mathcal D,z)$ be a family indexed by ordered sets $O\subseteq V$: each $\mathcal D_{O,t}$ ($0<t\le 1$) is a probability distribution on the independent subsets of $O$, $\mathcal D_{\emptyset,t}(\emptyset)=1$, and the accepting masses $z_{O,e,t}(A)$ are measurable in $t$ and zero outside $e\in O$, $A\subseteq O-e$. Then $(\mathcal D,z)$ is realizable by an ordinal algorithm in the continuous-time model (its accepted-set distributions and accepting masses are $\mathcal D$ at every positive horizon and $z$ almost everywhere in time, for every value order) **if and only if** it satisfies capacity (8) and consistency (9). Moreover every such feasible family is realized by accepting the current arrival $e$ at time $t$, from accepted set $A$, with probability
--   $$q_{O,e,t}(A)=\frac{z_{O,e,t}(A)}{\mathcal D_{O-e,t}(A)},\qquad 0/0=0. \tag{10}$$
--
--   This reduces the design of an optimal ordinal algorithm to constructing a feasible family; Theorem 5.2 does so for the survivor distributions.
--
--   Differences from the source:
--   - reading: ordinal algorithm in the continuous-time model using observations so far and private randomness → a behavioural rule (observed ordered set, history with times and decisions, current element and time) ↦ acceptance probability, clipped to [0, 1], 0 when dependent; jointly measurable in past arrival times and the current time for each fixed discrete history; reason: measurable randomized decisions with perfect recall admit this behavioural representation; this is an algorithm requirement, not an added hypothesis on the family
--   - encoding: footnote 2, accepting masses identified up to null sets of times → capacity and equality of accepting masses hold almost everywhere on (0,1); D is matched at every t in (0,1], including the continuous terminal value; reason: preserves the stated equivalence of accepting masses; modifying z on a null set changes neither consistency nor the induced distributions
--   - reading: standing description of D and z (probability distributions on independent sets, D_∅ = δ_∅, measurable z, zero outside supports) → hypothesis IsFamily; reason: these describe the objects the theorem is about
--   - reading: the integral in (9); the conditional probabilities defining the algorithm's D and z → required to exist: IntegrableOn (0, t] in Consistency; BoxIntegrable integrands in Realizes; reason: an equation between integrals presupposes them
--   - encoding: ordered sets; realizability for every value order; arrival-time ties → duplicate-free decreasing lists; every nonnegative v with label tie-breaking and every O ⊆ V; time ties broken by labels; reason: Lean convention, same instances
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 14, Theorem 4.4; standing assumptions p. 11 (§4)

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy
import Definitions.Def_EasyRankOne_Secretary_ContinuousTime

namespace EasyRankOne.Secretary

theorem theorem_4_4 {α : Type*} [Fintype α] [LinearOrder α] (M : Matroid α)
    (hE : M.E = Set.univ) (hrank : ∃ e, M.IsNonloop e)
    (D : List α → ℝ → Finset α → ℝ) (z : List α → α → ℝ → Finset α → ℝ)
    (hfam : IsFamily M D z) :
    ((∃ rule : Rule α, Realizes M rule D z) ↔ (Capacity M D z ∧ Consistency D z)) ∧
    (Capacity M D z ∧ Consistency D z → Realizes M (rule10 D z) D z) := by sorry

end EasyRankOne.Secretary
