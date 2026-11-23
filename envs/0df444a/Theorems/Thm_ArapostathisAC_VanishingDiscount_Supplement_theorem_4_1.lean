-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_4_1
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:05:17.775531+00:00
-- url     : https://prove2.me/theorems/c46766b5-1e13-4400-b04b-d8466c7f2cf7
-- title:
--   Theorem 4.1 (corrected: closed communicating classes in (ii) and (iv)) — on a finite state space: $J(f)=P^*(f)c(f)$, the rank of $I-P(f)$, and the normalized Poisson equations (4.1)–(4.2) with their u
-- statement:
--   Let $S$ be finite with $k$ states and let $f\in\Pi_{SD}$, with transition matrix $P=P(f)$, cost vector $c(f)=(c(i,f(i)))_i$, average cost vector $J(f)=(J(i,f))_i$ and Cesàro limit
--   $$P^*(f)=\lim_{N\to\infty}\frac1N\sum_{n=0}^{N-1}P^n(f).$$
--   Then the limit exists, $I-P+P^*$ is invertible, and
--
--   1. $J(f)=P^*(f)c(f)$;
--   2. the number of linearly independent equations in $(I-P(f))w=c(f)-J(f)$, the rank of $I-P(f)$, is $k$ minus the number of closed communicating classes of $P(f)$;
--   3. $v=J(f)$ and $w=w(f):=(I-P+P^*)^{-1}(I-P^*)c(f)$ solve
--   $$(4.1)\ \ (I-P(f))w=c(f)-v,\qquad (4.2)\ \ P^*(f)w=0;$$
--   4. $J(f)$ is constant on every closed communicating class, and $v=J(f)$, $w=w(f)$ are the unique solutions of (4.1)–(4.2) for which $v(s)=v(s')$ whenever $s,s'$ lie in the same closed communicating class and $v(s)=J(s,f)$ at every transient state $s$.
--
--   These are the gain–bias equations of a finite multichain Markov chain; they underlie the policy-iteration and Laurent-expansion methods of §4.
--
--   **Formalization Note** $P^*$ is the published `limitMatrix` (Cesàro limit) and the inverse is Mathlib's matrix inverse; the statement asserts the convergence and the invertibility, so neither is a junk value. $J(i,f)\in[0,\infty]$ is the expected average cost of the path measure; clause (i) shows it is finite, and (iii)–(iv) use its real value.
--
--   Differences from the source:
--   - generalization: §4.1 finite action sets → an arbitrary action space A; reason: the theorem concerns only P(f), c(f) and J(f) of a fixed f ∈ Π_SD; finite A is a special case
--   - generalization: the existence of P*(f), stated as well known before the theorem, and the inverse in w(f) → two additional conclusions: the Cesàro means converge to P*(f) and I − P(f) + P*(f) is invertible; reason: they make P* and the inverse genuine; both are true and specialize away
--   - correction: the number of communicating classes in (ii) → the number of closed communicating (recurrent) classes; reason: rank(I − P) = k minus the multiplicity of the eigenvalue 1, which is the number of recurrent classes; counting transient classes too is false for P = [[0,1],[0,1]] (classes {1},{2}, rank(I − P) = 1 = 2 − 1)
--   - reading: the number of linearly independent equations in (I − P(f))w = c(f) − J(f) → the rank of the matrix I − P(f); reason: the system is consistent by (iii), so its coefficient and augmented ranks agree
--   - correction: (iv) v = J(f), w = w(f) are the unique solutions of (4.1)–(4.2) with v(s) = v(s′) whenever s, s′ lie in the same communicating class (transient classes included) and v(s) = J(s, f) at transient s → J(f) is constant on every closed communicating class, and (J(f), w(f)) is the unique solution with v constant on every closed communicating class and v(s) = J(s, f) at every transient s; reason: the printed side condition fails for v = J(f) itself on a transient class: states 1, 2 transient and communicating, 1 → 2, 1 → 3, 2 → 1, 2 → 4 each with probability 1/2, states 3, 4 absorbing with costs 0 and 1 gives J(1) = 1/3 ≠ J(2) = 2/3, so the printed (iv) has no solution with v = J(f); "communicating class" is read as closed (recurrent) class, as in (ii); transient states are pinned by v(s) = J(s, f), so the uniqueness also covers every pair satisfying the printed condition
--   - encoding: J(i, f) as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 294, Theorem 4.1, (4.1)–(4.2); p. 294, definition of P*(f)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_FiniteChain

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet BlackwellDiscreteDP.NearOne

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 4.1 (p. 294). Finite state space `S` (`k = |S|` states); `f ∈ Π_SD` with transition
matrix `P = P(f)`, cost vector `c = c(f)`, Cesàro limit `P* = lim_N N⁻¹ ∑_{n<N} Pⁿ`, and
average cost vector `J(f) = (J(i, f))_i`. Then the Cesàro means converge to `P*`,
`I − P + P*` is invertible, and
(i) `J(f) = P* c(f)`;
(ii) the number of linearly independent equations in `(I − P)w = c − J(f)`, the rank of `I − P`,
is `k` minus the number of closed communicating classes of `P`;
(iii) `v = J(f)` and `w = w(f) := (I − P + P*)⁻¹ (I − P*) c(f)` solve (4.1) `(I − P)w = c − v` and
(4.2) `P* w = 0`;
(iv) `J(f)` is constant on every closed communicating class, and `v = J(f)`, `w = w(f)` are the
unique solutions of (4.1)–(4.2) with `v` constant on every closed communicating class and
`v(s) = J(s, f)` at every transient state `s`. -/
theorem theorem_4_1 {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (f : StationaryPolicy M) :
    Tendsto (cesaroMean (sdMatrix M f)) atTop (𝓝 (limitMatrix (sdMatrix M f))) ∧
    IsUnit (1 - sdMatrix M f + limitMatrix (sdMatrix M f)) ∧
    (∀ i, avgCost M f.toPolicy i =
      ENNReal.ofReal ((limitMatrix (sdMatrix M f) *ᵥ sdCost M f) i)) ∧
    (1 - sdMatrix M f).rank = Fintype.card S - numClosedClasses (sdMatrix M f) ∧
    ((1 - sdMatrix M f) *ᵥ
        (((1 - sdMatrix M f + limitMatrix (sdMatrix M f))⁻¹ * (1 - limitMatrix (sdMatrix M f)))
          *ᵥ sdCost M f) =
        sdCost M f - fun i => (avgCost M f.toPolicy i).toReal) ∧
    (limitMatrix (sdMatrix M f) *ᵥ
        (((1 - sdMatrix M f + limitMatrix (sdMatrix M f))⁻¹ * (1 - limitMatrix (sdMatrix M f)))
          *ᵥ sdCost M f) = 0) ∧
    (∀ s s', IsEssential (sdMatrix M f) s → Communicates (sdMatrix M f) s s' →
      avgCost M f.toPolicy s = avgCost M f.toPolicy s') ∧
    (∀ v w : S → ℝ, (1 - sdMatrix M f) *ᵥ w = sdCost M f - v →
      limitMatrix (sdMatrix M f) *ᵥ w = 0 →
      (∀ s s', IsEssential (sdMatrix M f) s → Communicates (sdMatrix M f) s s' → v s = v s') →
      (∀ s, ¬ IsEssential (sdMatrix M f) s → v s = (avgCost M f.toPolicy s).toReal) →
      v = (fun i => (avgCost M f.toPolicy i).toReal) ∧
        w = ((1 - sdMatrix M f + limitMatrix (sdMatrix M f))⁻¹ *
          (1 - limitMatrix (sdMatrix M f))) *ᵥ sdCost M f) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
