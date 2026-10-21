-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_lemma_3_7
-- name    : ExtFSMFG.Existence.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:27.30652+00:00
-- url     : https://prove2.me/theorems/ab55ea1d-57d5-4d6b-bf94-ea491e04b1e7
-- title:
--   Lemma 3.7, p. 9 — Ĥ and â are Lipschitz in z for ‖·‖_{X_{t−}} and in (p, ν) with a factor 1 + ‖z‖_{X_{t−}}
-- statement:
--   Assume $T>0$, $A\subseteq\mathbb R^l$ compact, and Assumptions 2.2, 2.7 and 3.4 with minimizer $\hat a$. Then there is a constant $C>0$ such that for every $t\in(0,T]$, every state $e_i$, all $p,p'\in\mathcal S$, $\nu,\nu'\in\mathcal P(A)$ and $z,z'\in\mathbb R^m$,
--   $$|\hat H_i(t,z,p,\nu)-\hat H_i(t,z',p',\nu')|\le C\|z-z'\|_{e_i}+C(1+\|z\|_{e_i})\big(\|p-p'\|+\mathcal W_1(\nu,\nu')\big),$$
--   $$\|\hat a_i(t,z,p)-\hat a_i(t,z',p')\|\le C\|z-z'\|_{e_i}+C(1+\|z\|_{e_i})\|p-p'\|.$$
--
--   These are the Lipschitz bounds (26)–(27) on the minimized Hamiltonian and the minimizer that make the BSDE (29) well posed and drive the continuity of the fixed-point map.
--
--   **Formalization Note** The paper states the bounds for all $(\omega,t)\in\Omega\times(0,T]$ through $X_{t-}$; since $X_{t-}$ ranges over $E$ and $\|\cdot\|_{X_{t-}}=\|\cdot\|_{e_i}$ when $X_{t-}=e_i$, this is the same as the per-state form above, with one constant for all states.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 9, Lemma 3.7 (26)–(27)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem lemma_3_7 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A)
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l))
    (h22 : Assumption22 T A q) (h27 : Assumption27 T A f g) (h34 : Assumption34 T A q f ahat) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ≥0, 0 < t → t ≤ T → ∀ (i : Fin m),
      ∀ p ∈ stdSimplex ℝ (Fin m), ∀ p' ∈ stdSimplex ℝ (Fin m), ∀ (ν ν' : PA A) (z z' : Fin m → ℝ),
        |Hhat q f t i z p ν - Hhat q f t i z' p' ν'| ≤
            C * seminormE i (z - z') + C * (1 + seminormE i z) * (eucl (p - p') + W1 ν ν') ∧
          ‖ahat t i z p - ahat t i z' p'‖ ≤
            C * seminormE i (z - z') + C * (1 + seminormE i z) * eucl (p - p') := by sorry

end ExtFSMFG.Existence
