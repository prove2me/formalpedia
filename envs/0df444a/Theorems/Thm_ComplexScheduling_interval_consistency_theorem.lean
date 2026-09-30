-- Prove2me | Theorems.Thm_ComplexScheduling_interval_consistency_theorem
-- name    : ComplexScheduling.interval_consistency_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:22:02.786665+00:00
-- url     : https://prove2.me/theorems/24bc9dd1-7bcb-4b0c-a2c5-2613a96dbe31
-- title:
--   Theorem 3.7 — the interval consistency theorem for disjunctive sets
-- statement:
--   Consider an RCPSP instance with conjunction set $C$, disjunction set $D$ and time windows
--   $[r_i,d_i]$, and let $I$ be a disjunctive set for $(C,D)$: at least two activities, any two of
--   which are related by a disjunction or a conjunction, so that no two of them can be processed
--   at the same time. Let $J\subseteq I$, let $J'$ and $J''$ be proper subsets of $J$ with
--   $J'\cup J''\ne\emptyset$, and write $P(J)=\sum_{i\in J}p_i$. If
--
--   $$
--   \max_{\substack{\nu\in J\setminus J',\ \mu\in J\setminus J''\\ \nu\ne\mu}}\bigl(d_\mu-r_\nu\bigr)\;<\;P(J) ,
--   \tag{3.121}
--   $$
--
--   then in every feasible schedule — feasible for the RCPSP, satisfying the conjunctions $C$ and
--   the disjunctions $D$, and within the time windows — an activity from $J'$ starts first in $J$
--   or an activity from $J''$ ends last in $J$.
--
--   This is Theorem 3.7, the general result from which the interval consistency tests of Section
--   3.6.4 (input, output, input-or-output, and the two negation tests) are read off by choosing
--   $J'$ and $J''$. If neither conclusion held, the activity of $J$ starting first would be some
--   $\nu\notin J'$ and the one ending last some $\mu\notin J''$, so all of $J$ would be processed
--   inside $[r_\nu,d_\mu]$, an interval too short for $P(J)$ non-overlapping activities.
--
--   **Formalization Note** The maximum in (3.121) is stated as the equivalent family
--   $d_\mu<r_\nu+P(J)$ over the same index pairs, which has no junk value when the index set is
--   empty (the family is then vacuous, as a maximum over an empty set, $-\infty$, would make it) and
--   no natural-number subtraction. "Starts first" and "ends last" are read with $\le$; on a
--   disjunctive set with positive durations this is the strict reading, and the statement remains
--   true without positivity, so none is assumed: the book invokes positivity only to justify
--   restricting to $\nu\ne\mu$, and in the case where that restriction empties the index set the
--   conclusion holds outright. The RCPSP feasibility of the schedule is the book's "feasible" and
--   is carried as a hypothesis, although the argument uses only the windows and the disjunctions.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.4, printed p. 169 (PDF p. 179), Theorem 3.7: "Let I be a disjunctive set and J′, J′′ ⊂ J ⊆ I with J′ ∪ J′′ ≠ ∅. If max_{ν∈J\J′, μ∈J\J′′, ν≠μ} (d_μ − r_ν) < P(J), (3.121) then in J an activity from J′ must start first or an activity from J′′ must end last in any feasible schedule."

import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem interval_consistency_theorem {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (J J' J'' : Finset (Fin n)) (hJI : J ⊆ I) (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hne : (J' ∪ J'').Nonempty)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'', ν ≠ μ → dl μ < rel ν + totalProcessing p J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by sorry
end ComplexScheduling
