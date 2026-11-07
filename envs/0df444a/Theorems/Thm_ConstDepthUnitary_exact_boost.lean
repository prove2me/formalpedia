-- Prove2me | Theorems.Thm_ConstDepthUnitary_exact_boost
-- name    : ConstDepthUnitary.exact_boost
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:44.539961+00:00
-- url     : https://prove2.me/theorems/2d964c94-a80c-47da-a962-9e188dfbc3d5
-- title:
--   Theorem 7.1 — boosting to an exact implementation
-- statement:
--   There are universal constants $C_0,C_1,C_2,c$ with the following property. Let $C$ be a circuit with fan-out on $n$ target qubits and $m$ ancillas, let $U$ be an $n$-qubit unitary, and let $A=(I\otimes\langle0^m|)C(I\otimes|0^m\rangle)$. If
--   $$\|U-A\|\le\frac1{10\cdot2^{n/2}},$$
--   then there is a circuit $D$ with fan-out on $n$ target qubits and $m'$ ancillas with
--   $$(I\otimes\langle0^{m'}|)D(I\otimes|0^{m'}\rangle)=U,$$
--   $m'\le C_1m\log_2m+C_2\,4^n(\log_2(4^n+2))^c$, and $\operatorname{depth}(D)\le3\operatorname{depth}(C)+C_0$.
--
--   So an approximation of exponentially small but explicit error is turned into an exact implementation at a constant-factor cost in depth.
--
--   Differences from the source:
--   - encoding: constants hidden in O(·) → an existential constant quantified before all data; reason: the paper's constants are universal
--   - reading: Õ(4^n) → C₂·4^n·(log₂(4^n + 2))^c; reason: the paper does not define Õ; this is g·polylog(g), not zero at n = 0
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 7.1, p.43

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_zeroBlock
open scoped Matrix.Norms.L2Operator

namespace ConstDepthUnitary

/-- Theorem 7.1: if a depth-`d`, `n`-qubit, `m`-ancilla circuit `C` with fan-out has zero-ancilla block `A` with
`‖U − A‖ ≤ 1/(10 · 2^{n/2})`, then a circuit `D` with fan-out has zero-ancilla block exactly `U`, with
`m′ = O(m log m) + Õ(4ⁿ)` ancillas and depth `3d + O(1)`. All constants are universal.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 7.1, p.43.

**Formalization Note** `logb 2 m = 0` at `m = 0, 1`; there the term `Õ(4ⁿ)` covers `D`'s ancillas. -/
theorem exact_boost :
    ∃ (C₀ : ℕ) (C₁ C₂ : ℝ) (c : ℕ), ∀ (n m : ℕ) (C : Circuit (Fin n ⊕ Fin m))
        (U : Matrix.unitaryGroup (Fin n → Bool) ℂ),
      ‖(U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - zeroBlock C‖ ≤
          1 / (10 * (2 : ℝ) ^ ((n : ℝ) / 2)) →
      ∃ (m' : ℕ) (D : Circuit (Fin n ⊕ Fin m')),
        zeroBlock D = (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∧
        (m' : ℝ) ≤ C₁ * m * Real.logb 2 m + C₂ * 4 ^ n * Real.logb 2 ((4 : ℝ) ^ n + 2) ^ c ∧
        D.depth ≤ 3 * C.depth + C₀ := by sorry

end ConstDepthUnitary
