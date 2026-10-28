-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_rounding_error
-- name    : CliffordTApprox.Ancilla.rounding_error
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:08.132395+00:00
-- url     : https://prove2.me/theorems/8b9882ee-ddf5-4a1d-88d2-e1aa9c14d6bb
-- title:
--   §2.2, p. 3 — the rounding γ of e^{iφ} with denominator 2^k satisfies |γ − e^{iφ}| ≤ √2/2^k
-- statement:
--   Let $k \in \mathbb N$, $0 \le \varphi \le \pi/4$, and
--   $$\gamma = \frac{\lfloor 2^k\cos\varphi\rfloor + i\lfloor 2^k\sin\varphi\rfloor}{2^k}.$$
--   Then
--   $$|\gamma - e^{i\varphi}| \le \frac{\sqrt 2}{2^k}.$$
--
--   The bound controls the first term of the distance between the prepared state and $e^{i\varphi}|00\rangle$; it is $O(1/2^{2k})$ after squaring.
--
--   **Formalization Note.** The constant $\sqrt2/2^k$ is the one printed on the page. The hypothesis $0\le\varphi\le\pi/4$ is the standing assumption of §2.1.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 3, §2.2

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2.2, p. 3: `|γ − e^{iφ}| ≤ √2 / 2^k` for `0 ≤ φ ≤ π/4`. -/
theorem rounding_error (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ≤ Real.sqrt 2 / 2 ^ k := by sorry

end CliffordTApprox.Ancilla
