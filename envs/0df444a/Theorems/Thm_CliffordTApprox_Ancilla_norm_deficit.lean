-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_norm_deficit
-- name    : CliffordTApprox.Ancilla.norm_deficit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:01.260185+00:00
-- url     : https://prove2.me/theorems/f13fd7a9-3226-4289-9a83-0284a81dd9c5
-- title:
--   §2.2, p. 3 — ‖g‖² = 1 − |γ|², |γ| ≤ 1 and 1 − |γ|² ≤ 2√2/2^k (the page: O(1/2^k))
-- statement:
--   Let $k\in\mathbb N$, $0\le\varphi\le\pi/4$ and $\gamma = (\lfloor 2^k\cos\varphi\rfloor + i\lfloor 2^k\sin\varphi\rfloor)/2^k$. Then
--   1. $|\gamma| \le 1$;
--   2. $$1 - |\gamma|^2 \le \frac{2\sqrt2}{2^k};$$
--   3. for all integers $a,b,c,d$ with $a^2+b^2+c^2+d^2 = 4^k - \lfloor 2^k\cos\varphi\rfloor^2 - \lfloor 2^k\sin\varphi\rfloor^2$, the squared norm of $|g\rangle = ((a+ib)|0\rangle + (c+id)|1\rangle)/2^k$ equals $1-|\gamma|^2$:
--   $$\frac{a^2+b^2+c^2+d^2}{4^k} = 1 - |\gamma|^2 .$$
--
--   Together with the rounding bound, this shows that the part of $|v\rangle$ outside $\gamma|00\rangle$ has squared norm $O(1/2^k)$.
--
--   **Formalization Note.** The page states $1-|\gamma|^2 \in O(1/2^k)$ and obtains it from the triangle inequality $||\gamma| - |e^{i\varphi}|| \le |\gamma - e^{i\varphi}|$; the constant $2\sqrt2$ is pinned from that step together with $|\gamma - e^{i\varphi}|\le\sqrt2/2^k$ and $1 + |\gamma| \le 2$.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 3, §2.2

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.2, p. 3: for `0 ≤ φ ≤ π/4`, `|γ| ≤ 1`, the deficit `1 − |γ|²` is at most `2√2 / 2^k`
(the page: `O(1/2^k)`), and for every solution of the four-square equation the squared norm
`‖g‖² = (a² + b² + c² + d²)/4^k` of the tail `|g⟩` equals `1 − |γ|²`. -/
theorem norm_deficit (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    ‖gammaApprox k φ‖ ≤ 1 ∧
    1 - ‖gammaApprox k φ‖ ^ 2 ≤ 2 * Real.sqrt 2 / 2 ^ k ∧
    ∀ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ →
      ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ℝ) / 4 ^ k = 1 - ‖gammaApprox k φ‖ ^ 2 := by sorry

end CliffordTApprox.Ancilla
