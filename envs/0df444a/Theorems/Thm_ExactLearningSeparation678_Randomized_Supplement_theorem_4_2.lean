-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_4_2
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:24.332217+00:00
-- url     : https://prove2.me/theorems/293195c2-cef9-47f4-809f-2617b8b058af
-- title:
--   Theorem 4.2 (companion theorem) — $R_{\mathrm{bool}}(C_m)=1$ but $R(C_m)=\Omega(\log m)$
-- statement:
--   Let $C_m=\{c_1,\dots,c_m\}$ be the dictator class on the domain $\{0,1\}^m$, $c_j(z)=z_j$. There is an absolute $c>0$ such that for every integer $m\ge2$: the domain has $2^m$ points (so $C_m\subseteq\{0,1\}^{2^m}$), $|C_m|=m$,
--   $$R_{\mathrm{bool}}(C_m)=1\qquad\text{and}\qquad R(C_m)\ge c\log m.$$
--   Here $R$ is the randomized membership-query complexity of exact learning and $R_{\mathrm{bool}}(C)=\max_{P\subseteq C}R(b_P)$ the largest randomized query complexity of deciding $b_P(c)=1[c\in P]$.
--
--   So the classical analogue of quantum Booleanization (Theorem 4.1) fails.
--
--   **Formalization Note** The constant precedes $m$. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: for every m ≥ 2 there is C_m ⊆ {0,1}^{2^m} with |C_m| = m, R_bool(C_m) = 1, R(C_m) = Ω(log m) → the explicit dictator class of the proof, on the coordinate type Fin m → Bool of cardinality 2^m, with one c > 0 before every m ≥ 2; reason: the proof supplies this witness; the explicit quantifiers retain the entire existential conclusion
--   - encoding: bounded-error quantum and randomized query complexities Q(C), R(C) → the published quantumExactComplexity (QueryAlg, XOR oracle, any finite workspace) and classicalExactComplexity (randomized decision trees, worst-case query bound), success ≥ 2/3 on every target; reason: the mission’s published models of the source’s Q and R
--   - encoding: logarithms of unspecified base → natural logarithm Real.log; reason: a change of base is absorbed into the absolute constant
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 4.2, p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Models

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 4.2 (Randomized separation), p.30, for the dictator classes of its proof: for every
`m ≥ 2` the domain `{0,1}^m` has `2^m` points, `|C_m| = m`, `R_bool(C_m) = 1`, and one absolute
`c > 0` (fixed before `m`) gives `R(C_m) ≥ c log m`. -/
theorem theorem_4_2 : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
    Fintype.card (Fin m → Bool) = 2 ^ m ∧ (dictatorClass m).card = m ∧
    Rbool (dictatorClass m) = 1 ∧
    c * Real.log (m : ℝ) ≤ (classicalExactComplexity (dictatorClass m) : ℝ) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
