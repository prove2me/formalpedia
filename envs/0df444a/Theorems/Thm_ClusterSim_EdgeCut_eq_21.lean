-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_eq_21
-- name    : ClusterSim.EdgeCut.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:08.797762+00:00
-- url     : https://prove2.me/theorems/5264049b-cd0f-4c18-9cde-32d38ba75d1f
-- title:
--   Eq. (21) — every 2×2 matrix is A = Σ_{i=1}^8 c_i Tr(A O_i) ρ_i
-- statement:
--   Let $O_i,\rho_i,c_i$ ($i=1,\dots,8$) be the Pauli observables, eigenprojectors and coefficients of eqs. (12)–(19), and $\Phi_i(A)=\operatorname{Tr}(AO_i)\rho_i$ the measure-and-prepare maps of eq. (20). Then for every complex $2\times2$ matrix $A$,
--   $$A=\sum_{i=1}^8 c_i\,\Phi_i(A)=\sum_{i=1}^8 c_i\operatorname{Tr}(AO_i)\,\rho_i .$$
--
--   Equivalently (eq. (22)), the identity channel on a qubit is a signed combination of eight measure-and-prepare channels; this is the decomposition that cutting an edge relies on.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 8, proof of Lemma 1, eq. (21)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_PauliData

namespace ClusterSim.EdgeCut

/-- Eq. (21), p. 8: every `2 × 2` complex matrix is the combination `A = Σ_{i=1}^8 c_i Φ_i(A)` of the
measure-and-prepare maps `Φ_i(A) = Tr(A O_i) ρ_i` of eq. (20), with the data (12)–(19). -/
theorem eq_21 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A = ∑ i : Fin 8, (coef i : ℂ) • measPrep i A := by sorry

end ClusterSim.EdgeCut
