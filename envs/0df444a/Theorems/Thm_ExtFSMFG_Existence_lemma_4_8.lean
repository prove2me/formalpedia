-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_lemma_4_8
-- name    : ExtFSMFG.Existence.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:32.423991+00:00
-- url     : https://prove2.me/theorems/3c487bf3-f619-4fed-9d2d-39345d14e330
-- title:
--   Lemma 4.8, p. 16 — the randomized rate q̲ and Hamiltonian Ĥ̲ are Lipschitz in W̄₁
-- statement:
--   Assume $T>0$, $A$ compact, Assumptions 2.2, 2.7, 3.4 and the regularity of $f,q$. There is $C>0$ such that for every $t\in(0,T]$, all states $e_i,e_j$, $p,p'\in\mathcal S$, $\alpha,\alpha'\in A$, $z,z'\in\mathbb R^m$ and $m,m'\in\mathcal P(\mathcal P(A))$,
--   $$|\underline q(t,i,j,\alpha,p,m)-\underline q(t,i,j,\alpha',p',m')|\le C\big(\|\alpha-\alpha'\|+\|p-p'\|+\bar{\mathcal W}_1(m,m')\big),\qquad(38)$$
--   $$|\underline{\hat H}_i(t,z,p,m)-\underline{\hat H}_i(t,z',p',m')|\le C\|z-z'\|_{e_i}+C(1+\|z\|_{e_i})\big(\|p-p'\|+\bar{\mathcal W}_1(m,m')\big).\qquad(39)$$
--
--   These are the randomized analogues of Assumption 2.2(iii) and Lemma 3.7, used for the well-posedness of (41) and the continuity of $\Phi$.
--
--   **Formalization Note** As in Lemma 3.7, the bound through $X_{t-}$ is stated per state. $\bar{\mathcal W}_1$ is the coupling distance with marginals $m,m'$ (the printed (40) omits the marginal constraint).
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 16, Lemma 4.8 (38)–(39), (40) p. 17

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE
import Definitions.Def_ExtFSMFG_Existence_FixedPoint

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem lemma_4_8 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A)
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l))
    (h22 : Assumption22 T A q) (h27 : Assumption27 T A f g) (h34 : Assumption34 T A q f ahat)
    (hreg : RegularData T A q f) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ≥0, 0 < t → t ≤ T → ∀ (i j : Fin m),
      ∀ p ∈ stdSimplex ℝ (Fin m), ∀ p' ∈ stdSimplex ℝ (Fin m), ∀ a ∈ A, ∀ a' ∈ A,
      ∀ (z z' : Fin m → ℝ) (mη mη' : ProbabilityMeasure (PA A)),
        |qbar q t i j a p mη - qbar q t i j a' p' mη'| ≤
            C * (‖a - a'‖ + eucl (p - p') + W1bar mη mη') ∧
          |Hhatbar q f t i z p mη - Hhatbar q f t i z' p' mη'| ≤
            C * seminormE i (z - z') + C * (1 + seminormE i z) * (eucl (p - p') + W1bar mη mη') := by sorry

end ExtFSMFG.Existence
