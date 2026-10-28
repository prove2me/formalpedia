-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_eqs_27_28
-- name    : ClusterSim.EdgeCut.eqs_27_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:03.49383+00:00
-- url     : https://prove2.me/theorems/fe7903a2-1cf5-497b-a105-4c332e4a4921
-- title:
--   Eqs. (27)–(28) — S = Σ_{i=1}^8 c_i (O_i ⊗ ρ_i) = ½(I⊗I + X⊗X + Y⊗Y + Z⊗Z) is the SWAP operator
-- statement:
--   With the data $O_i,\rho_i,c_i$ of eqs. (12)–(19), let $S=\sum_{i=1}^8 c_i\,(O_i\otimes\rho_i)$, a $4\times4$ matrix. Then
--   $$S=\tfrac12\big(I\otimes I+X\otimes X+Y\otimes Y+Z\otimes Z\big)=\begin{pmatrix}1&0&0&0\\0&0&1&0\\0&1&0&0\\0&0&0&1\end{pmatrix},$$
--   the two-qubit SWAP operator, whose entry in row $(a,b)$ and column $(c,d)$ (with $a,b,c,d\in\{0,1\}$) is $1$ if $a=d$ and $b=c$, and $0$ otherwise.
--
--   This identity is the matrix form of the verification of eq. (23) in the proof of Lemma 1.
--
--   **Formalization Note** The tensor product is the Kronecker product indexed by `Fin 2 × Fin 2` (row $(a,b)$ is the basis vector $|a\rangle\otimes|b\rangle$, ordered 00, 01, 10, 11 as in (28)).
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 9, proof of Lemma 1, eqs. (27)–(28)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_PauliData

namespace ClusterSim.EdgeCut

open Matrix Kronecker

/-- Eqs. (27)–(28), p. 9: `S = Σ_{i=1}^8 c_i (O_i ⊗ ρ_i)` equals `½(I⊗I + X⊗X + Y⊗Y + Z⊗Z)`, and this
is the two-qubit SWAP operator, whose entry at row `(a, b)` and column `(c, d)` is `1` if
`a = d` and `b = c` and `0` otherwise. -/
theorem eqs_27_28 :
    (∑ i : Fin 8, (coef i : ℂ) • (pauli i ⊗ₖ eigProj i)) =
        (1 / 2 : ℂ) • (pauliI ⊗ₖ pauliI + pauliX ⊗ₖ pauliX + pauliY ⊗ₖ pauliY + pauliZ ⊗ₖ pauliZ) ∧
      (1 / 2 : ℂ) • (pauliI ⊗ₖ pauliI + pauliX ⊗ₖ pauliX + pauliY ⊗ₖ pauliY + pauliZ ⊗ₖ pauliZ) =
        Matrix.of (fun (x y : Fin 2 × Fin 2) => if x.1 = y.2 ∧ x.2 = y.1 then (1 : ℂ) else 0) := by sorry

end ClusterSim.EdgeCut
