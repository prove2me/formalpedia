-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_lemma7_14_lsc_iff_monotone_limit
-- name    : BertsekasShreve.SemicontSelection.lemma7_14_lsc_iff_monotone_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:43.631204+00:00
-- url     : https://prove2.me/theorems/6e993e65-d3e1-48d2-97b6-09288976aec5
-- title:
--   Lemma 7.14 — semicontinuous bounded-below functions are increasing limits of bounded continuous functions
-- statement:
--   Let $X$ be a metrizable space and $f:X\to R^*$. Write $C(X)$ for the space of bounded continuous real-valued functions on $X$.
--
--   1. $f$ is lower semicontinuous and bounded below (by some real number $b$) if and only if there is a sequence $\{f_n\}\subset C(X)$ with $f_n\uparrow f$, that is, $f_1\le f_2\le\cdots$ pointwise and $f_n(x)\to f(x)$ in $R^*$ for every $x$.
--   2. $f$ is upper semicontinuous and bounded above (by some real number) if and only if there is a sequence $\{f_n\}\subset C(X)$ with $f_n\downarrow f$.
--
--   The lemma reduces statements about semicontinuous functions to statements about continuous ones through monotone limits; it is the step that turns Proposition 7.30 into Proposition 7.31.
--
--   **Formalization Note** "Bounded below" means bounded below by a real number: in `EReal` every function is bounded below by $\bot$, so `BddBelow` would be vacuous and is not used. $C(X)$ is `BoundedContinuousFunction X ℝ`; convergence $f_n(x)\to f(x)$ is in the order topology of `EReal`, so $f(x)=+\infty$ is allowed.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 147, Lemma 7.14; C(X) as defined in Section 7.1, p. 103

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.14 (Bertsekas & Shreve, p. 147). Let `X` be metrizable and `f : X → R*`.
(a) `f` is lower semicontinuous and bounded below (by a real number) iff there is a sequence
`f_n` of bounded continuous real functions with `f_n ↑ f` pointwise.
(b) `f` is upper semicontinuous and bounded above iff there is such a sequence with `f_n ↓ f`. -/
theorem lemma7_14_lsc_iff_monotone_limit {X : Type*} [TopologicalSpace X] [MetrizableSpace X]
    (f : X → EReal) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g n x ≤ g (n + 1) x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ x, f x ≤ (b : EReal)) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g (n + 1) x ≤ g n x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) := by sorry

end BertsekasShreve.SemicontSelection
