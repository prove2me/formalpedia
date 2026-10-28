-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_eqs_23_30
-- name    : ClusterSim.EdgeCut.eqs_23_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:05.715184+00:00
-- url     : https://prove2.me/theorems/1197fa2d-88ea-442b-b6ef-274df2bde9df
-- title:
--   Eqs. (23)–(30) — _αA(I)_β = Σ_{i=1}^8 c_i · _αA(O_i) · A(ρ_i)_β = δ_{α,β} for all α, β ∈ Π
-- statement:
--   For edge indices $\alpha,\beta\in\Pi=\{0,1\}^2$, let $_\alpha A(I)_\beta$ be the tensor (6) of the identity gate, $_\alpha A(O)$ the tensor (7) of an observable and $A(\rho)_\beta$ the tensor (5) of a state. With the data of eqs. (12)–(19),
--   $${}_\alpha A(I)_\beta=\sum_{i=1}^8 c_i\cdot{}_\alpha A(O_i)\cdot A(\rho_i)_\beta=\delta_{\alpha,\beta}\qquad\text{for all }\alpha,\beta\in\Pi .$$
--
--   This is the local identity behind Lemma 1: inserting the identity gate on an edge does not change the value of a network, and the identity gate's tensor splits into an observable on the edge's source side and a state on its target side.
--
--   **Formalization Note** The page says "According to Eq. (7)" for the evaluation (24) of the left-hand side; the identity-gate tensor is eq. (6) with $U=I$, which is what is formalized. The value $\delta_{\alpha,\beta}$ is as printed.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 9, proof of Lemma 1, eqs. (23)–(30) (reference in (24) corrected from Eq. (7) to Eq. (6))

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_TensorNetwork
import Definitions.Def_ClusterSim_EdgeCut_PauliData

namespace ClusterSim.EdgeCut

/-- Eqs. (23)–(30), p. 9: for all edge indices `α, β ∈ Π`, the tensor (6) of the identity gate
equals the eight-term combination of an observable tensor (7) and a state tensor (5),
`_αA(I)_β = Σ_{i=1}^8 c_i · _αA(O_i) · A(ρ_i)_β`, and both equal `δ_{α,β}`. -/
theorem eqs_23_30 (a b : Idx) :
    gateTensor 1 a b = ∑ i : Fin 8, (coef i : ℂ) * obsTensor (pauli i) a * stateTensor (eigProj i) b ∧
      gateTensor 1 a b = if a = b then 1 else 0 := by sorry

end ClusterSim.EdgeCut
