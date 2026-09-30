-- Prove2me | Theorems.Thm_ComplexScheduling_disjunctive_set_infeasibility_test
-- name    : ComplexScheduling.disjunctive_set_infeasibility_test
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:18:42.166988+00:00
-- url     : https://prove2.me/theorems/95f6a4f9-db71-41fe-8c46-38571efdb511
-- title:
--   The first infeasibility test — a disjunctive subset whose windows are shorter than its processing time
-- statement:
--   Consider an RCPSP instance with conjunction set $C$, disjunction set $D$ and time windows
--   $[r_i,d_i]$, and let $I$ be a disjunctive set for $(C,D)$. If some nonempty subset $J\subseteq I$
--   satisfies
--
--   $$
--   \max_{\mu\in J}d_\mu\;-\;\min_{\nu\in J}r_\nu\;<\;P(J)=\sum_{i\in J}p_i ,
--   $$
--
--   then no feasible schedule exists: there is no schedule that is feasible for the RCPSP, respects
--   the conjunctions $C$ and the disjunctions $D$, and lies within the time windows.
--
--   This is the first infeasibility test of Section 3.6.4. The activities of $J$ cannot overlap,
--   so they need $P(J)$ units of time inside the interval $[\min_\nu r_\nu,\max_\mu d_\mu]$, whose
--   length is smaller.
--
--   **Formalization Note** The inequality between a maximum and a minimum is stated as the
--   equivalent family of inequalities $d_\mu<r_\nu+P(J)$ for all $\mu,\nu\in J$, which avoids
--   natural-number subtraction and needs no separate treatment of a negative difference. $J$ must
--   be nonempty, as the maximum and minimum presuppose; for $J=\emptyset$ the family is vacuous
--   and the conclusion would be false. No positivity of the processing times is needed: a
--   zero-length activity contributes nothing to $P(J)$ and nothing to the packing.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.4, printed p. 169 (PDF p. 179): "If there is a subset J ⊆ I with max_{μ∈J} d_μ − min_{ν∈J} r_ν < P(J), then obviously no feasible schedule exists since all jobs from the subset J have to be processed in the interval [min_{ν∈J} r_ν, max_{μ∈J} d_μ], which does not have the capacity P(J)."

import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem disjunctive_set_infeasibility_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (J : Finset (Fin n)) (hJI : J ⊆ I) (hJ : J.Nonempty)
    (hcond : ∀ μ ∈ J, ∀ ν ∈ J, dl μ < rel ν + totalProcessing p J) :
    ¬ ∃ S : Fin n → ℕ, FeasibleSchedule p Rcap demand prec S ∧ RespectsArcs p C S ∧
      SatisfiesDisjunctions p D S ∧ WithinWindows rel dl p S := by sorry
end ComplexScheduling
