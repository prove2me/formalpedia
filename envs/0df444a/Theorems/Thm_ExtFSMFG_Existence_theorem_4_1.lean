-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_theorem_4_1
-- name    : ExtFSMFG.Existence.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:22.640429+00:00
-- url     : https://prove2.me/theorems/013091f7-0723-45b3-8d3e-359ecb456987
-- title:
--   Theorem 4.1, p. 12 — under Assumptions 2.2, 2.7 and 3.4 the extended finite state mean field game has a Nash equilibrium in the weak formulation
-- statement:
--   Let $T>0$, let $A\subseteq\mathbb R^l$ be compact, let $p^\circ$ be a probability vector on the $m$ states, and let $\mathbb P$ be the reference measure on the canonical space $\Omega$ of càdlàg paths $[0,T]\to\{e_1,\dots,e_m\}$ continuous at $T$, under which the canonical process is a Markov chain with initial law $p^\circ$ and all off-diagonal rates equal to $1$. Let $q(t,i,j,\alpha,p,\nu)$ be transition rates, $f(t,e_i,\alpha,p,\nu)$ a running cost and $g(e_i,p)$ a terminal cost, depending on time, the state, the control $\alpha\in A$, the state distribution $p\in\mathcal S$ and the distribution of controls $\nu\in\mathcal P(A)$. Assume:
--   1. Assumption 2.2 (Q-matrix, rates bounded between $C_1>0$ and $C_2$ off the diagonal, rates Lipschitz in $(\alpha,p,\nu)$ with $\mathcal W_1$ in $\nu$);
--   2. Assumption 2.7 (running and terminal costs Lipschitz);
--   3. Assumption 3.4 (the reduced Hamiltonian $H_i(t,z,\cdot,p,\nu)$ has a unique minimizer $\hat a_i(t,z,p)$ over $A$, independent of $\nu$, measurable and Lipschitz as in (21));
--   4. $q$ and $f$ are jointly measurable and $f$ is bounded.
--
--   Then there exist a strategy $\alpha^*\in\mathbb A$ (an $\mathbb F$-predictable $A$-valued process) and measurable flows $p^*:[0,T]\to\mathcal S$, $\nu^*:[0,T]\to\mathcal P(A)$ forming a Nash equilibrium in the sense of Definition 2.8:
--   $$J(\alpha^*,p^*,\nu^*)\le J(\alpha,p^*,\nu^*)\ \ \text{for all }\alpha\in\mathbb A,\qquad p^*_t=\big(\mathbb Q^{(\alpha^*,p^*,\nu^*)}[X_t=e_i]\big)_{i},\qquad \nu^*_t=\mathbb Q^{(\alpha^*,p^*,\nu^*)}_{\#\alpha^*_t}$$
--   for every $t\in[0,T]$, where $\mathbb Q^{(\alpha,p,\nu)}$ is the law under which $X$ jumps from $e_i$ to $e_j$ at rate $q(t,i,j,\alpha_t,p_t,\nu_t)$ (Girsanov density (7)) and $J$ is the cost (12).
--
--   This is the main existence result of the paper: equilibria exist among all closed-loop, path-dependent strategies, with rates and costs that may depend on the distribution of controls.
--
--   **Formalization Note** Item 4 is used but not stated by the paper. The reference measure is a hypothesis characterized by its finite-dimensional distributions. The equilibrium is stated directly through Definition 2.8 (the cost $J$, the measures $\mathbb Q^{(\alpha,p,\nu)}$ and laws); the fixed-point map of the proof does not appear.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 12, Theorem 4.1 (with Definition 2.8, p. 7)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model

open MeasureTheory
open scoped NNReal

namespace ExtFSMFG.Existence

theorem theorem_4_1 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A)
    (p₀ : stdSimplex ℝ (Fin m)) (P : Measure (Omega m T)) [IsProbabilityMeasure P]
    (hP : IsReference T p₀ P)
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l))
    (h22 : Assumption22 T A q) (h27 : Assumption27 T A f g) (h34 : Assumption34 T A q f ahat)
    (hreg : RegularData T A q f) :
    ∃ (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) (p : ℝ≥0 → Fin m → ℝ) (ν : ℝ≥0 → PA A),
      IsNashEq T A P q f g α p ν := by sorry

end ExtFSMFG.Existence
