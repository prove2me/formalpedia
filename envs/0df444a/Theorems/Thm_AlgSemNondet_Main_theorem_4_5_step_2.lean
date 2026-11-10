-- Prove2me | Theorems.Thm_AlgSemNondet_Main_theorem_4_5_step_2
-- name    : AlgSemNondet.Main.theorem_4_5_step_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:46:08.442989+00:00
-- url     : https://prove2.me/theorems/5dc2a444-f218-4d8f-a93c-a723482c2ee2
-- title:
--   Theorem 4.5, proof Step 2 — $\sqrt2$ and $\sqrt3$ are incommensurable over $\mathbb Q$
-- statement:
--   The algebraic numbers $\sqrt 2$ and $\sqrt 3$ are both nonzero and linearly independent over $\mathbb Q$, i.e. incommensurable over $\mathbb Q$ (Definition 3.11). Under the encoding $0 \mapsto 1$, $1 \mapsto 2$, $\alpha \mapsto \sqrt2$, $\beta \mapsto \sqrt3$ of Step 1, this is the fact that $\varepsilon(\alpha\beta) = \{\sqrt2, \sqrt3\}$ contains an incommensurable pair.
--
--   Differences from the source:
--   - encoding: the algebraic numbers √2 and √3 → the complex numbers ((Real.sqrt 2 : ℝ) : ℂ) and ((Real.sqrt 3 : ℝ) : ℂ); reason: encodings take values in ℂ, where the algebraic numbers live in this formalization
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Theorem 4.5, proof Step 2, p.18, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_Incommensurable

namespace AlgSemNondet.Main

/-- Theorem 4.5, proof Step 2: `√2` and `√3` are nonzero and linearly independent over `ℚ`
(incommensurable), as elements of `ℂ`. -/
theorem theorem_4_5_step_2 :
    Incommensurable ℚ ((Real.sqrt 2 : ℝ) : ℂ) ((Real.sqrt 3 : ℝ) : ℂ) := by sorry

end AlgSemNondet.Main
