-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_proposition_4_10
-- name    : ExtFSMFG.Existence.proposition_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:27.685294+00:00
-- url     : https://prove2.me/theorems/4a09adbe-9f24-4a37-9554-3437ba4457ca
-- title:
--   Proposition 4.10, p. 18 — for some C₀ > 0 the set 𝒫̄₀ × ℛ₀ is stable for the map Φ
-- statement:
--   Assume $T>0$, $A$ compact, $\mathbb P$ the reference measure, Assumptions 2.2, 2.7, 3.4 and the regularity of $f,q$. There is a constant $C_0>0$ such that, with $\bar{\mathcal P}_0$ the closure in $\mathcal P$ of $\mathcal P_0$ of (35), the set $\bar{\mathcal P}_0\times\mathcal R_0$ is stable for $\Phi$: for every $\mu\in\bar{\mathcal P}_0$, every $\eta=\mathcal L(dt)\times\eta_t(dm)\in\mathcal R_0$ and every $(\mu',\eta')$ with $\Phi(\mu,\eta)=(\mu',\eta')$,
--   $$\mu'\in\bar{\mathcal P}_0\quad\text{and}\quad\eta'\in\mathcal R_0 .$$
--
--   This is the invariance of the compact convex set required by Schauder's fixed point theorem.
--
--   **Formalization Note** $C_0$ is "specified later (see the proof of Proposition 4.10)" on p. 13, so the statement asserts its existence. The input $\eta\in\mathcal R_0$ is given by a measurable disintegration $t\mapsto\eta_t\in\mathcal P(\mathcal P(A))$, and $\Phi$ by its graph.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 18, Proposition 4.10, (35), (41)–(46)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE
import Definitions.Def_ExtFSMFG_Existence_FixedPoint

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem proposition_4_10 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A)
    (p₀ : stdSimplex ℝ (Fin m)) (P : Measure (Omega m T)) [IsProbabilityMeasure P]
    (hP : IsReference T p₀ P)
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l))
    (h22 : Assumption22 T A q) (h27 : Assumption27 T A f g) (h34 : Assumption34 T A q f ahat)
    (hreg : RegularData T A q f) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ mu ∈ closure (P0set P C₀),
      ∀ ηt : ℝ≥0 → ProbabilityMeasure (PA A), (Measurable fun t : Set.Icc (0 : ℝ≥0) T => ηt t) →
      ∀ (mu' : PD m T) (η' : Rstable T A), PhiGraph P q f g ahat mu ηt mu' η' →
        mu' ∈ closure (P0set P C₀) ∧ η' ∈ R0set T A := by sorry

end ExtFSMFG.Existence
