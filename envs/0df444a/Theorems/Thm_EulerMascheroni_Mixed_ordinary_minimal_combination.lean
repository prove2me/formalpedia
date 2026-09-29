-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_ordinary_minimal_combination
-- name    : EulerMascheroni.Mixed.ordinary_minimal_combination
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T19:45:16.144987+00:00
-- url     : https://prove2.me/theorems/15c7eda2-9f8a-47cf-b349-dccdd8819afa
-- title:
--   Every nonzero Euler E-combination has a minimal equation ordinary at one
-- statement:
--   For any complex $a,b,c$, not all zero, the formal combination $F=a+b e^X+c e^X\operatorname{Ein}(X)$ admits a positive-order minimal scalar polynomial differential equation whose leading coefficient is nonzero at $X=1$.
--
--   If $c\ne0$, use the explicit minimal third-order operator. If $c=0$ and $a,b\ne0$, use $D^2-D$, whose minimality follows from independence of $1$ and $e^X$. A nonzero multiple of $e^X$ has minimal equation $D-1$, and a nonzero constant has minimal equation $D$. Thus this proves the entire ordinary cyclic-combination step needed for the Euler E-system at one, including all degenerate cases. No algebraicity hypothesis on $a,b,c$ and no arithmetic zero theorem are used.
-- source:
--   Direct scalar elimination in the Euler E-system; the ordinary cyclic-combination step in Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2, pp. 6–7. Minimality uses the separately proved polynomial functional independence of 1, exp(X), and exp(X) Ein(X).

import Definitions.Def_eulerScalarEquation
open ArithmeticE EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.ordinary_minimal_combination (a b c : ℂ) (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ (p : ℕ → Polynomial ℂ) (n : ℕ), 0 < n ∧
      MinimalEquation p n (formalCombination a b c) ∧ (p n).eval 1 ≠ 0 := by sorry
