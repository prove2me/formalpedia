-- Prove2me | Theorems.Thm_ComplexScheduling_input_or_output_test
-- name    : ComplexScheduling.input_or_output_test
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:20:56.448323+00:00
-- url     : https://prove2.me/theorems/a90a8a9f-2dcf-4150-9a80-6aadcf7ebfdb
-- title:
--   Input-or-output test — i starts first or j ends last, and i → j when i ≠ j
-- statement:
--   Consider an RCPSP instance with conjunction set $C$, disjunction set $D$ and time windows
--   $[r_i,d_i]$, let $I$ be a disjunctive set for $(C,D)$ whose activities have positive processing
--   times, let $J\subseteq I$ have at least two elements, and let $i,j\in J$. If
--
--   $$
--   \max_{\mu\in J\setminus\{j\}}d_\mu\;-\;\min_{\nu\in J\setminus\{i\}}r_\nu\;<\;P(J) ,
--   $$
--
--   then in every feasible schedule — feasible for the RCPSP, satisfying $C$ and $D$, within the
--   windows — activity $i$ starts first in $J$ or activity $j$ ends last in $J$; and if $i\ne j$
--   then $i\to j$, that is, $S_i+p_i\le S_j$.
--
--   This is the input-or-output test, the instance $J'=\{i\}$, $J''=\{j\}$ of Theorem 3.7 in its
--   form (3.122) without the restriction $\nu\ne\mu$. The conjunction $i\to j$ follows in either
--   case: if $i$ starts first it cannot overlap $j$ and so finishes before $j$ starts, and if $j$
--   ends last the same disjunction, read the other way, again forces $i$ before $j$.
--
--   **Formalization Note** The condition is the family $d_\mu<r_\nu+P(J)$ over $\mu\in J\setminus\{j\}$,
--   $\nu\in J\setminus\{i\}$. The requirement $|J|\ge 2$ is the book's $\{i\},\{j\}\subset J$ (proper
--   subsets); with $J=\{i\}$ the index sets would be empty and the first conclusion still holds
--   trivially, but the book does not state the test there. Positivity of the processing times on
--   $I$ is what the conjunction $i\to j$ needs.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.4, printed p. 170 (PDF p. 180), the input-or-output test: "Let J′ = {i} and J′′ = {j} with i, j ∈ J. Then condition (3.122) can be rewritten as max_{μ∈J\{j}} d_μ − min_{ν∈J\{i}} r_ν < P(J). If this condition holds, then activity i must start first in J or activity j must end last in J, i.e. i is input for J or j is output for J. If i ≠ j, the conjunction i → j is implied."

import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem input_or_output_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (J : Finset (Fin n)) (hJI : J ⊆ I) (hJ : 2 ≤ J.card) (i j : Fin n) (hi : i ∈ J) (hj : j ∈ J)
    (hcond : ∀ μ ∈ J.erase j, ∀ ν ∈ J.erase i, dl μ < rel ν + totalProcessing p J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    (StartsFirstIn S J i ∨ EndsLastIn p S J j) ∧ (i ≠ j → S i + p i ≤ S j) := by sorry
end ComplexScheduling
