-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_same_maximizers
-- name    : DiophantinePreprocessing.FrankTardos.same_maximizers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:42:49.963966+00:00
-- url     : https://prove2.me/theorems/56fe3a11-31a0-4dfe-9022-7f88b15b333f
-- title:
--   Lemma 4.1 (i) — sign-equivalent objectives have the same maximizers over $\{Ax \le b\}$
-- statement:
--   Let $A$ be an $m \times n$ matrix with entries in $\{0, +1, -1\}$, let $b \in \mathbb{R}^m$ and $P = \{x \in \mathbb{R}^n : Ax \le b\}$. Let $w', w'' \in \mathbb{R}^n$ be vectors such that
--   $$\operatorname{sign}(w' \cdot h) = \operatorname{sign}(w'' \cdot h)$$
--   for every integral vector $h \in \mathbb{Z}^n$ with $\|h\|_1 \le (n+1)!$. Then a point $x \in P$ is $w'$-maximal if and only if it is $w''$-maximal.
--
--   Two objectives that agree in sign on all small integral directions therefore define the same set of optimal solutions of $\max\{wx : Ax \le b\}$ over every polyhedron with a $0, \pm1$ constraint matrix.
--
--   **Formalization Note** The restriction to $0, \pm 1$ matrices is the standing assumption of Section 4 (p. 56); the lemma's statement does not repeat it but relies on it (it is where $(n+1)!$ comes from). $\|h\|_1$ is the explicit sum $\sum_j |h(j)|$.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 57, Lemma 4.1 (i); standing assumption of Sect. 4, p. 56

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_IsWMaximal

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Lemma 4.1 (i) (p. 57): let `A` be a matrix with entries `0, ±1` and let
`w', w''` satisfy `sign (w' · h) = sign (w'' · h)` for every integer `h` with
`‖h‖₁ ≤ (n+1)!`. Then a point of `P = {x : A x ≤ b}` is `w'`-maximal iff it is `w''`-maximal. -/
theorem same_maximizers (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (b : Fin m → ℝ)
    (w' w'' : Fin n → ℝ)
    (hsign : ∀ h : Fin n → ℤ, ∑ j, |h j| ≤ ((n + 1).factorial : ℤ) →
      SignType.sign (∑ j, w' j * (h j : ℝ)) = SignType.sign (∑ j, w'' j * (h j : ℝ))) :
    ∀ x : Fin n → ℝ, IsWMaximal A b w' x ↔ IsWMaximal A b w'' x := by sorry

end DiophantinePreprocessing.FrankTardos
