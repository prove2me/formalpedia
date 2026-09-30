-- Prove2me | Theorems.Thm_ComplexScheduling_output_test
-- name    : ComplexScheduling.output_test
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:20:13.776418+00:00
-- url     : https://prove2.me/theorems/3050115e-cfa2-49f5-ad45-0663d956417b
-- title:
--   Output test (3.124) — an activity that must be scheduled last in Ω ∪ {i}
-- statement:
--   Consider an RCPSP instance with conjunction set $C$, disjunction set $D$ and time windows
--   $[r_i,d_i]$, let $I$ be a disjunctive set for $(C,D)$ whose activities have positive processing
--   times, let $\Omega\subseteq I$ be nonempty and let $i\in I\setminus\Omega$. If
--
--   $$
--   \max_{\mu\in\Omega}d_\mu\;-\;\min_{\nu\in\Omega\cup\{i\}}r_\nu\;<\;P(\Omega)+p_i ,
--   $$
--
--   then in every feasible schedule — feasible for the RCPSP, satisfying $C$ and $D$, within the
--   windows — every activity of $\Omega$ is processed before $i$: $S_j+p_j\le S_i$ for all
--   $j\in\Omega$. In the book's notation, $\Omega\to i$: $i$ is an **output** of $\Omega\cup\{i\}$.
--
--   This is the output test, the instance $J'=\emptyset$, $J''=\{i\}$ of Theorem 3.7, and the
--   mirror image of the input test: if some $\mu\in\Omega$ ended last, all of $\Omega\cup\{i\}$
--   would have to fit between the smallest head and $d_\mu$, an interval too short for
--   $P(\Omega)+p_i$; so $i$ ends last, and since it cannot overlap any $j\in\Omega$, $j$ finishes
--   before $i$ starts.
--
--   **Formalization Note** The condition is the family $d_\mu<r_\nu+P(\Omega\cup\{i\})$ over
--   $\mu\in\Omega$, $\nu\in\Omega\cup\{i\}$. Positive processing times on $I$ are what turn "ends
--   last" into the conjunctions $j\to i$, exactly as in the input test.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.4, printed p. 170 (PDF p. 180), the output test, and printed p. 171 (PDF p. 181), implication (3.124): "Symmetrically, max_{μ∈Ω} d_μ − min_{ν∈Ω∪{i}} r_ν < P(Ω) + p_i ⇒ Ω → i, i.e. i has to be scheduled last in Ω ∪ {i}. ... in the case (3.124) we may introduce the additional conjunctions j → i for all j ∈ Ω."

import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem output_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (Ω : Finset (Fin n)) (hΩ : Ω ⊆ I) (hne : Ω.Nonempty) (i : Fin n) (hi : i ∈ I) (hiΩ : i ∉ Ω)
    (hcond : ∀ μ ∈ Ω, ∀ ν ∈ insert i Ω, dl μ < rel ν + totalProcessing p (insert i Ω))
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    ∀ j ∈ Ω, S j + p j ≤ S i := by sorry
end ComplexScheduling
