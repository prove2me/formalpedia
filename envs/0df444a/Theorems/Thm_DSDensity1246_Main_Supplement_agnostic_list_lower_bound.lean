-- Prove2me | Theorems.Thm_DSDensity1246_Main_Supplement_agnostic_list_lower_bound
-- name    : DSDensity1246.Main.Supplement.agnostic_list_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T06:26:53.511206+00:00
-- url     : https://prove2.me/theorems/a2ca52f2-318f-41cc-bd86-873bf9bcfc0a
-- title:
--   Theorem 8 — Agnostic List Learning Lower Bound (both clauses)
-- statement:
--   Both of the following agnostic list-learning lower bounds hold. Each class is chosen before the learner and the numerical parameters; only the hard distribution may depend on them. All learners may use arbitrary independent randomness and must output lists of size at most ℓ.
--
--   1. For every ℓ≥1 there is a class H with scale-ℓ Natarajan and DS dimensions both exactly 1. For every learner A, 0<ε,δ<1/8, and natural m with
--
--   $$m\le\frac{\log(1/(8\delta))}{64\varepsilon^2},$$
--
--   there is a distribution D such that
--
--   $$\Pr_{S\sim D^m,r}\!\left[\operatorname{err}_D(A(S,r))>\inf_{h\in H}\operatorname{err}_D(h)+\varepsilon\right]>\delta.$$
--
--   2. For every ℓ,d≥1 there is a class H with scale-ℓ Natarajan dimension exactly d. For every learner A, 0<ε<1/64, and natural m with
--
--   $$m\le\frac{\ell d}{32768\varepsilon^2},$$
--
--   there is a distribution D such that
--
--   $$\Pr_{S\sim D^m,r}\!\left[\operatorname{err}_D(A(S,r))>\inf_{h\in H}\operatorname{err}_D(h)+\varepsilon\right]>\frac1{10}.$$
--
--   The comparator in both clauses is a single-label hypothesis. Together these statements give the confidence and dimension contributions to the agnostic lower rate, with all printed constants and strict inequalities retained.
--
--   Differences from the source:
--   - encoding: probabilities over iid data and independent internal randomness, compared to the infimum single-hypothesis error → Mathlib probability measures on arbitrary labeled data spaces, finite product sampling with an independent seed law, outer probabilities of arbitrary events, and an ENNReal single-hypothesis infimum; reason: no countability, finite-support, measurability, or attainment restriction is introduced; measurable cases agree with ordinary probability and the empty-class infimum is infinity
--   - encoding: existential hypothesis classes in both clauses → classes on ℕ with 2ℓ labels in clause (1), and on Fin d × ℕ with labels Fin ℓ × Bool in clause (2), with Natarajan dimension in ℕ∞; reason: these are the witness carriers constructed on pp.33 and37; Boolean signs encode ±1 and the existential classes precede every learner and parameter
--   - encoding: arbitrary randomized learners, with no confidence parameter in clause (2) → all seed spaces and probability laws and all bounded-list maps, evaluated at the confidence input 1/10 in clause (2); reason: every learner in the source is represented by a map ignoring the optional confidence input, so no learner is excluded
--   - encoding: the proof constructs finitely supported hard distributions → the existential hard data law is required to carry the all-sets σ-algebra; reason: the source finite atomic witnesses are defined on every subset, so data errors are genuine measurable probabilities; arbitrary learner seed spaces and all source instances remain covered
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 33, Theorem 8; proof pp. 33-42

import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_Supplement_natarajan
import Definitions.Def_DSDensity1246_Main_Supplement_learning

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- Theorem 8, p.33: both clauses together, retaining every explicit constant.
The existential classes are on the countable carriers used in the proof;
randomized learners and their seed laws are unrestricted. -/
theorem agnostic_list_lower_bound :
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∃ H : Set (ℕ → Fin (2 * ℓ)),
      listNatDim ℓ H = 1 ∧ listDSDim ℓ H = 1 ∧
      ∀ (R : Type*) [MeasurableSpace R] (ρ : ProbabilityMeasure R)
        (A : ListLearner ℕ (Fin (2 * ℓ)) R ℓ),
        ∀ ε δ : ℝ, 0 < ε → ε < 1 / 8 → 0 < δ → δ < 1 / 8 →
          ∀ m : ℕ, (m : ℝ) ≤ Real.log (1 / (8 * δ)) / (64 * ε ^ 2) →
            ∃ D : DataLaw (ℕ × Fin (2 * ℓ)), D.1 = ⊤ ∧
              ENNReal.ofReal δ < failureProbability D ρ A ε δ m (bestError D H)) ∧
    (∀ ℓ d : ℕ, 1 ≤ ℓ → 1 ≤ d →
      ∃ H : Set ((Fin d × ℕ) → (Fin ℓ × Bool)), listNatDim ℓ H = d ∧
      ∀ (R : Type*) [MeasurableSpace R] (ρ : ProbabilityMeasure R)
        (A : ListLearner (Fin d × ℕ) (Fin ℓ × Bool) R ℓ),
        ∀ ε : ℝ, 0 < ε → ε < 1 / 64 →
          ∀ m : ℕ, (m : ℝ) ≤ (ℓ : ℝ) * d / (32768 * ε ^ 2) →
            ∃ D : DataLaw ((Fin d × ℕ) × (Fin ℓ × Bool)), D.1 = ⊤ ∧
              ENNReal.ofReal (1 / 10 : ℝ) <
                failureProbability D ρ A ε (1 / 10) m (bestError D H)) := by sorry

end DSDensity1246.Main.Supplement
