-- Prove2me | Theorems.Thm_FiniteStateContract_Equivalence_lemma_3_3
-- name    : FiniteStateContract.Equivalence.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:14:45.064661+00:00
-- url     : https://prove2.me/theorems/d72fbe64-1fe4-4829-940b-dc1b8f1412af
-- title:
--   Lemma 3.3 — Uniform Lipschitz bounds for the Hamiltonian and optimizer
-- statement:
--   Under the §2 setting and Assumptions 2.1 and 3.1, there is one constant $C>0$ such that for every path $\omega$, time $t\in(0,T]$, reward argument $R\in\mathbb R$, distribution $p\in\mathcal S$, and vectors $z,z'\in\mathbb R^m$,
--   $$|\hat H(t,X_{t-},z,p,R)-\hat H(t,X_{t-},z',p,R)|\le C\|z-z'\|_{X_{t-}},$$
--   $$\|\hat a(t,X_{t-},z,p)-\hat a(t,X_{t-},z',p)\|\le C\|z-z'\|_{X_{t-}}.$$
--   The same positive constant works in both estimates, uniformly over all the displayed variables. It may depend on the model data. The action norm is the Euclidean norm for arbitrary dimension $l$.
--
--   Differences from the source:
--   - encoding: basis-vector states and paths on [0,T] → Fin m labels and nonnegative real time, with canonical paths frozen after T; reason: the published path space is in bijection with the source space; the initial simplex vector excludes m=0 and retains m=1
--   - reading: the right side of (15) is written with a hat → evaluate the unminimized Hamiltonian H at its unique minimizer; reason: the printed argument count and preceding sentence uniquely identify H; recorded in insight I4
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), Lemma 3.3, PDF p. 6 = printed p. 6; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_FiniteStateContract_Equivalence_Model

open MeasureTheory
open scoped NNReal

namespace FiniteStateContract.Equivalence

open ExtFSMFG.Existence (Omega Xm seminormE)

theorem lemma_3_3 {m l : ℕ} {T : ℝ≥0} (D : Data m l T) (a : Feedback m l)
    (hS : Setting D) (h21 : Assumption21 D) (h31 : Assumption31 D a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Omega m T) (t : ℝ≥0), 0 < t → t ≤ T →
      ∀ (R : ℝ) (p : stdSimplex ℝ (Fin m)) (z z' : Vec m),
        |Hhat D a t (Xm t ω) z p R - Hhat D a t (Xm t ω) z' p R| ≤
          C * seminormE (Xm t ω) (z - z') ∧
        ‖a t (Xm t ω) z p - a t (Xm t ω) z' p‖ ≤
          C * seminormE (Xm t ω) (z - z') := by sorry

end FiniteStateContract.Equivalence
