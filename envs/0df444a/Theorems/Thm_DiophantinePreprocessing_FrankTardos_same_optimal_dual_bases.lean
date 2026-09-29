-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_same_optimal_dual_bases
-- name    : DiophantinePreprocessing.FrankTardos.same_optimal_dual_bases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:43:21.120685+00:00
-- url     : https://prove2.me/theorems/33ff5aa9-f5cd-4730-b841-2e7f1048804d
-- title:
--   Lemma 4.1 (ii) — sign-equivalent objectives have the same optimal dual bases
-- statement:
--   Let $A$ be an $m \times n$ matrix with entries in $\{0, +1, -1\}$ and $b \in \mathbb{R}^m$. Let $w', w'' \in \mathbb{R}^n$ be vectors such that
--   $$\operatorname{sign}(w' \cdot h) = \operatorname{sign}(w'' \cdot h)$$
--   for every integral vector $h \in \mathbb{Z}^n$ with $\|h\|_1 \le (n+1)!$. Then a dual basis $B$ of $A$ is an optimal dual basis for $\max\{w'x : Ax \le b\}$ if and only if it is an optimal dual basis for $\max\{w''x : Ax \le b\}$.
--
--   Together with part (i), this shows that the whole optimal primal–dual structure of the linear program depends on the objective only through the signs it assigns to small integral vectors.
--
--   **Formalization Note** "Optimal dual basis" is the definition `IsOptimalDualBasis`: a maximal linearly independent set of row indices whose basic dual solution (supported on $B$) exists and is optimal for (1b). The $0, \pm1$ hypothesis is the standing assumption of Section 4 (p. 56).
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 57, Lemma 4.1 (ii); standing assumption of Sect. 4, p. 56

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_IsOptimalDualBasis

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Lemma 4.1 (ii) (p. 57): let `A` be a matrix with entries `0, ±1` and let
`w', w''` satisfy `sign (w' · h) = sign (w'' · h)` for every integer `h` with
`‖h‖₁ ≤ (n+1)!`. Then a dual basis `B` is optimal for `w = w'` iff it is optimal for
`w = w''`. -/
theorem same_optimal_dual_bases (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (b : Fin m → ℝ)
    (w' w'' : Fin n → ℝ)
    (hsign : ∀ h : Fin n → ℤ, ∑ j, |h j| ≤ ((n + 1).factorial : ℤ) →
      SignType.sign (∑ j, w' j * (h j : ℝ)) = SignType.sign (∑ j, w'' j * (h j : ℝ))) :
    ∀ B : Finset (Fin m), IsDualBasis A B →
      (IsOptimalDualBasis A b w' B ↔ IsOptimalDualBasis A b w'' B) := by sorry

end DiophantinePreprocessing.FrankTardos
