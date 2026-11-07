-- Prove2me | Theorems.Thm_ConstDepthUnitary_all_unitaries_shallow
-- name    : ConstDepthUnitary.all_unitaries_shallow
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:40.143513+00:00
-- url     : https://prove2.me/theorems/37fa3846-f222-4ff4-9d92-0cbd28477f86
-- title:
--   Theorem 6.1 — all unitaries have shallow circuits
-- statement:
--   There are universal constants such that for every $n$, every unitary $U$ on $N=2^n$ dimensions and every $\varepsilon>0$, with $L=\log_2(2+N/\varepsilon)$:
--
--   1. a circuit of one- and two-qubit gates, of depth $O(\log N+\log L+1)$ and width $\tilde O(N^2L^4)$, with
--   $$\|U\otimes|0\rangle-C_U(I\otimes|0\rangle)\|\le\varepsilon;$$
--   2. a circuit of one- and two-qubit gates and fan-out gates of size $O(NL^2)$, of depth $O(1)$ and width $\tilde O(N^2L^4)$, with the same bound.
--
--   Here $\tilde O(g)$ means $Cg(\log_2(g+2))^c$.
--
--   Differences from the source:
--   - reading: log(N/ϵ) for every ϵ > 0 → Lg(N, ε) = log₂(2 + N/ε); reason: log log(N/ϵ) is undefined or negative when ϵ is near or above N; for N ≥ 2, ε ≤ 1 they are within a constant
--   - reading: depth O(log N + log log(N/ϵ)), width Õ(·) → ≤ C(log₂ N + log₂ Lg + 1), and C·g·(log₂(g + 2))^c, with universal C, c; reason: the + 1 keeps the bound positive at N = 1; the paper does not define Õ
--   - encoding: U ∈ U(N) → U on 2^n dimensions; reason: a qubit register has dimension 2^n
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, p.35

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_ImplementsWithin
import Definitions.Def_ConstDepthUnitary_Lg

namespace ConstDepthUnitary

/-- Theorem 6.1 (all unitaries have shallow circuits): for every `U ∈ U(2ⁿ)` and `ε > 0`,
(1) a circuit of one- and two-qubit gates of depth `O(log N + log log(N/ε))` and width `Õ(N² log(N/ε)⁴)` with Eq. (70), and
(2) a circuit with `O(N log(N/ε)²)`-sized fan-out gates of depth `O(1)` and the same width with Eq. (70).
All constants are universal.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, p.35.

**Formalization Note** `log(N/ε)` is read as `Lg(N, ε) = log₂(2 + N/ε)`, for every `ε > 0`. The `+ 1` keeps the depth bound
positive at `N = 1`. The width counts target and ancilla qubits. -/
theorem all_unitaries_shallow :
    (∃ (C : ℝ) (c : ℕ), ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∀ U : Matrix.unitaryGroup (Fin n → Bool) ℂ,
      ∃ (m : ℕ) (D : Circuit (Fin n ⊕ Fin m)),
        D.IsStandard ∧
        (D.depth : ℝ) ≤ C * (Real.logb 2 ((2 : ℝ) ^ n) + Real.logb 2 (Lg ((2 : ℝ) ^ n) ε) + 1) ∧
        ((n + m : ℕ) : ℝ) ≤ C * (((2 : ℝ) ^ n) ^ 2 * Lg ((2 : ℝ) ^ n) ε ^ 4) *
          Real.logb 2 (((2 : ℝ) ^ n) ^ 2 * Lg ((2 : ℝ) ^ n) ε ^ 4 + 2) ^ c ∧
        ImplementsWithin D (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ε) ∧
    (∃ (d₀ : ℕ) (C : ℝ) (c : ℕ), ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∀ U : Matrix.unitaryGroup (Fin n → Bool) ℂ,
      ∃ (m : ℕ) (D : Circuit (Fin n ⊕ Fin m)),
        D.depth ≤ d₀ ∧
        (D.maxFanout : ℝ) ≤ C * (2 : ℝ) ^ n * Lg ((2 : ℝ) ^ n) ε ^ 2 ∧
        ((n + m : ℕ) : ℝ) ≤ C * (((2 : ℝ) ^ n) ^ 2 * Lg ((2 : ℝ) ^ n) ε ^ 4) *
          Real.logb 2 (((2 : ℝ) ^ n) ^ 2 * Lg ((2 : ℝ) ^ n) ε ^ 4 + 2) ^ c ∧
        ImplementsWithin D (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ε) := by sorry

end ConstDepthUnitary
