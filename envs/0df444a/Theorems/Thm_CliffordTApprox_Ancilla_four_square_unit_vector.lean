-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_four_square_unit_vector
-- name    : CliffordTApprox.Ancilla.four_square_unit_vector
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:58.840204+00:00
-- url     : https://prove2.me/theorems/24855e73-d095-4d29-9f1d-a84ca69fa4d6
-- title:
--   §2.1, p. 3 — a² + b² + c² + d² = 4^k − ⌊2^k cos φ⌋² − ⌊2^k sin φ⌋² is solvable and every solution makes |v⟩ a unit vector
-- statement:
--   Let $k \in \mathbb N$ and $0 \le \varphi \le \pi/4$, and let
--   $$D = 4^k - \lfloor 2^k\cos\varphi\rfloor^2 - \lfloor 2^k\sin\varphi\rfloor^2 .$$
--   Then:
--   1. $D \ge 0$;
--   2. the equation $a^2 + b^2 + c^2 + d^2 = D$ has a solution in integers $a, b, c, d$ (Lagrange's four-square theorem);
--   3. for every integer solution $(a,b,c,d)$, the vector
--   $$|v\rangle = \frac{1}{2^k}\big(\lfloor 2^k\cos\varphi\rfloor + i\lfloor 2^k\sin\varphi\rfloor,\ 0,\ a+ib,\ c+id\big)$$
--   is a unit vector of $\mathbb C^4$.
--
--   This is the reduction of the approximation problem to a sum of four squares: the vector $|v\rangle$, whose entries are Gaussian integers over $2^k$, is the state the circuit $C$ prepares.
--
--   **Formalization Note.** Floors are integer floors. The hypothesis $0 \le \varphi \le \pi/4$ is the paper's standing assumption of §2.1; it makes both floors nonnegative, and without it $D$ can be negative.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 3, §2.1 (the definition of |v⟩, the four-square equation and Lagrange's theorem)

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.1, p. 3: for `0 ≤ φ ≤ π/4` the right-hand side `4^k − ⌊2^k cos φ⌋² − ⌊2^k sin φ⌋²`
is a nonnegative integer, it is a sum of four integer squares (Lagrange), and every solution
`(a, b, c, d)` makes `|v⟩` a unit vector. -/
theorem four_square_unit_vector (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    0 ≤ deficit k φ ∧
    (∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ) ∧
    ∀ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ →
      IsState (vecV k φ a b c d) := by sorry

end CliffordTApprox.Ancilla
