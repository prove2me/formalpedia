-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_quantum_one_time_pad
-- name    : EFI1PRS.Uniform.quantum_one_time_pad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:03:40.332771+00:00
-- url     : https://prove2.me/theorems/efa167da-9f44-485a-a3f8-b72dc52cce8b
-- title:
--   Fact 2.14 — quantum one-time pad with side information
-- statement:
--   Let $D$ be a $d$-qubit register, $A$ any nonzero finite-dimensional side register, and $Y_{AD}$ any normalized state, including entangled states. With $P_{u,v}=\bigotimes_{j=1}^{d}X^{u_j}Z^{v_j}$,
--
--   $$\frac1{4^d}\sum_{u,v\in\{0,1\}^d}(I_A\otimes P_{u,v})Y(I_A\otimes P_{u,v})^\dagger=\operatorname{Tr}_D(Y)\otimes\mathsf{MM}_D.$$
--
--   The statement includes $d=0$ and a trivial side register. It is the full quantum mask identity used on the coherent construction; it does not require a pure input or absence of side information.
--
--   Differences from the source: none.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Fact 2.14, PDF/printed p. 9

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem quantum_one_time_pad {A : Type*} [Fintype A] [Nonempty A]
    (d : ℕ) (Y : Matrix (A × Qubits d) (A × Qubits d) ℂ) (hY : IsDensityMatrix Y) :
    ((4 : ℂ)^d)⁻¹ • (∑ u : Qubits d, ∑ v : Qubits d,
      let P := Matrix.kronecker (1 : Matrix A A ℂ) (pauliMask u v)
      P * Y * Pᴴ) = Matrix.kronecker (traceRight Y) (maximallyMixed d) := by sorry

end EFI1PRS.Uniform
