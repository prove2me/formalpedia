-- Prove2me | Theorems.Thm_BeliefDominance_dynamic_consistency
-- name    : BeliefDominance.dynamic_consistency
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:25:39.239639+00:00
-- url     : https://prove2.me/theorems/2a6650f8-7269-4306-b18d-467bc845661d
-- title:
--   Belief dominance is weakly consistent, immune to fallacious inconsistency, but not to fallible inconsistency
-- statement:
--   Let $\Phi$ be any set of discrete beliefs on signal–outcome pairs, in any two-period decision problem whose expected utilities (1) exist. Then belief dominance is weakly consistent, and it does not exhibit fallacious inconsistency:
--
--   $$
--   x^*\in X^*\ \Longrightarrow\ x_2^*(y)\in X^*_{2,x_1^*,y}\quad\text{for every signal }y.
--   $$
--
--   Fallible inconsistency, on the other hand, is not excluded: some decision problem of this kind exhibits it.
--
--   This is the paper's headline. Dominance over a set of beliefs falls between expected utility, which is fully consistent on positive-probability signals, and decision rules such as maxmin and minmax regret, which are fallaciously inconsistent. It holds for any set of priors and without a recursive formulation. The paper's witness for the last clause is the vaccine problem of §2.
--
--   Differences from the source:
--   - generalization: Theorem 5 alone: belief dominance is weakly consistent → Theorem 5 ∧ no fallacious inconsistency ∧ a problem with fallible inconsistency; reason: the first clause is Theorem 5; the others are the claim of the abstract and the introduction ("we prove"), through Theorem 3 and the §2 example
--   - generalization: §3.4 takes "each possible signal y ∈ 𝒴" to have a positive probability mass → not assumed: a belief of Φ may give y mass 0, and Φ_y may be empty; reason: the printed proof itself treats f ∈ Φ with f_Y(y) = 0, and the source's case is the one where no such f occurs; the §3.4 remark on zero-probability signals under expected utility concerns a second-period preference outside eq. (4), since here Φ_y = ∅ makes all actions indifferent
--   - reading: V(x, f) is written without comment, which presumes that the expectations exist → the hypothesis WellPosed: the sum (1) is summable for every f ∈ Φ and every x ∈ X; reason: Lean's tsum is 0 on a non-summable family, and the hypothesis covers exactly the strategies of X
--   - reading: ~_{x₁,y} and ≼_{x₁,y} are used on p.6 without a definition for belief dominance, and the generic ≺ of §3.2–3.3 is not spelled out → Indiff₂ is equality of V₂ on Φ_y, le₂ is Dominates₂ ∨ Indiff₂, and ≺ is strictPart; reason: analogy with the first-period definitions of p.5; le_isPreorder shows that dominance is exactly this strict part
--   - reading: in the formula for fallible inconsistency x₁* is unbound → x₁* is the first-period action of some x* ∈ X*; reason: "despite the first-period action being optimal" and clause (a) of the proof of Theorem 4, p.11
--   - encoding: discrete random variables, iterated sums, and the product over ŷ ≠ y → PMF (Y × Z), one sum over Y × Z, and strategies s ∈ X with s.1 = x₁*, s.2 y = a; reason: same instances; the sums agree under WellPosed, and the completions are the same
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, Theorem 5, p.7; abstract, p.1; introduction, p.2

import Mathlib
import Definitions.Def_BeliefDominance_Problem

universe u

namespace BeliefDominance

/-- Belief dominance is weakly consistent and therefore immune to fallacious inconsistency, but it
is not immune to fallible inconsistency (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic
Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, Theorem 5, p.7 (PDF p.8); abstract,
p.1 (PDF p.2); introduction, p.2 (PDF p.3)).

**Formalization Note** The first clause is Theorem 5 with its consequence through Theorem 3, for
every problem whose sums (1) exist: `Φ` is an arbitrary set of discrete beliefs on arbitrary types,
and signals of probability zero are allowed. The second clause is the abstract's "but not to the
less problematic fallible inconsistency"; the paper's witness is the vaccine problem of §2. -/
theorem dynamic_consistency :
    (∀ (A₁ A₂ Y Z : Type u) (P : Problem A₁ A₂ Y Z), P.WellPosed →
      WeaklyConsistent P.space P.le P.le₂ ∧ ¬ ExhibitsFallacious P.space P.le P.le₂) ∧
    (∃ (A₁ A₂ Y Z : Type) (P : Problem A₁ A₂ Y Z),
      P.WellPosed ∧ ExhibitsFallible P.space P.le P.le₂) := by sorry

end BeliefDominance
