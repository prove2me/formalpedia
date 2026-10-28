-- Prove2me | Theorems.Thm_ERealFn_exists_real_of_ne_top_ne_bot
-- name    : ERealFn.exists_real_of_ne_top_ne_bot
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:22:28.513992+00:00
-- url     : https://prove2.me/theorems/e14e1345-1972-4c76-8023-defbe7e4e82c
-- title:
--   An extended real that is neither $+\infty$ nor $-\infty$ is a real
-- statement:
--   If $e \in \overline{\mathbb{R}}$ satisfies $e \neq +\infty$ and $e \neq -\infty$, then there is a real number $r$ with $e = r$ (as the coercion $\mathbb{R} \hookrightarrow \overline{\mathbb{R}}$).
--
--   The statement is elementary, but the existential form is what makes it usable. In an argument
--   about extended-real-valued convex functions one typically establishes finiteness of a value
--   first -- properness gives $f \neq -\infty$ everywhere, and a separate step gives
--   $f(x) \neq +\infty$ at the point of interest -- and then wants to work with an actual real
--   number, so that `linarith` and `field_simp` apply. Obtaining the witness by destructuring this
--   statement avoids carrying `EReal.toReal` and its side conditions through the rest of the proof.
--
--   **Formalization Note** The witness is `e.toReal`, and the equation is `EReal.coe_toReal`
--   reversed. `EReal.toReal` is total, sending both infinities to `0`, so the hypotheses are what
--   make the conclusion say anything.
-- source:
--   Used repeatedly to move between `EReal` and `ℝ` in the objective-value estimates of Davis & Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017) 829-858, DOI 10.1007/s11228-017-0421-z, proof of Theorem 3.2, pp. 839-840.

import Mathlib

namespace ERealFn

/-- An extended real that is neither `⊤` nor `⊥` is the coercion of a real. -/
theorem exists_real_of_ne_top_ne_bot {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) :
    ∃ r : ℝ, e = r := by sorry

end ERealFn
