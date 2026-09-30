-- Prove2me | Theorems.Thm_ComplexScheduling_input_test
-- name    : ComplexScheduling.input_test
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:19:26.590019+00:00
-- url     : https://prove2.me/theorems/86a8a21f-775c-47c9-8654-4f52bdb0e7e5
-- title:
--   Input test (3.123) — an activity that must be scheduled first in Ω ∪ {i}
-- statement:
--   Consider an RCPSP instance with conjunction set $C$, disjunction set $D$ and time windows
--   $[r_i,d_i]$, let $I$ be a disjunctive set for $(C,D)$ whose activities have positive processing
--   times, let $\Omega\subseteq I$ be nonempty and let $i\in I\setminus\Omega$. If
--
--   $$
--   \max_{\mu\in\Omega\cup\{i\}}d_\mu\;-\;\min_{\nu\in\Omega}r_\nu\;<\;P(\Omega)+p_i ,
--   $$
--
--   then in every feasible schedule — feasible for the RCPSP, satisfying $C$ and $D$, within the
--   windows — activity $i$ is processed before every activity of $\Omega$: $S_i+p_i\le S_j$ for all
--   $j\in\Omega$. In the book's notation, $i\to\Omega$: $i$ is an **input** of $\Omega\cup\{i\}$.
--
--   This is the input test, the instance $J'=\{i\}$, $J''=\emptyset$ of Theorem 3.7. If some
--   $\nu\in\Omega$ started first, all of $\Omega\cup\{i\}$ would have to fit between $r_\nu$ and the
--   largest deadline, an interval too short for $P(\Omega)+p_i$; so $i$ starts first, and since it
--   cannot overlap any $j\in\Omega$, it finishes before $j$ starts.
--
--   **Formalization Note** The condition is the family $d_\mu<r_\nu+P(\Omega\cup\{i\})$ over
--   $\mu\in\Omega\cup\{i\}$, $\nu\in\Omega$, with $P(\Omega\cup\{i\})=P(\Omega)+p_i$ as $i\notin\Omega$.
--   Positive processing times on $I$ are needed for the conclusion $i\to j$: with $p_j=0$ an
--   activity $j$ could start at the same instant as $i$ without violating the disjunction. The book
--   takes positive durations for granted in this section, and this is the hypothesis that turns
--   "starts first" into a conjunction.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.4, printed p. 170 (PDF p. 180), the input test, and printed p. 171 (PDF p. 181), implication (3.123): "max_{μ∈Ω∪{i}} d_μ − min_{ν∈Ω} r_ν < P(Ω) + p_i ⇒ i → Ω, i.e. i has to be scheduled first in Ω ∪ {i}. ... In the case (3.123) we may introduce the additional conjunctions i → j for all j ∈ Ω."

import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem input_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (Ω : Finset (Fin n)) (hΩ : Ω ⊆ I) (hne : Ω.Nonempty) (i : Fin n) (hi : i ∈ I) (hiΩ : i ∉ Ω)
    (hcond : ∀ μ ∈ insert i Ω, ∀ ν ∈ Ω, dl μ < rel ν + totalProcessing p (insert i Ω))
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    ∀ j ∈ Ω, S i + p i ≤ S j := by sorry
end ComplexScheduling
