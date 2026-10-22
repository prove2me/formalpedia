-- Prove2me | Theorems.Thm_CliffordTApprox_Ancilla_composition
-- name    : CliffordTApprox.Ancilla.composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:09.168504+00:00
-- url     : https://prove2.me/theorems/06ef1a9c-6008-4e14-954c-aa8f0a09dca2
-- title:
--   §2, p. 2 — approximations compose: errors of successive circuits add on the initialized map
-- statement:
--   Let $C_1, C_2$ be circuits of gates from $\{H, T, \mathrm{CNOT}\}$ on three wires (data qubit, two ancillas), let $U_1, U_2$ be $2\times2$ matrices with $U_1$ unitary, and suppose
--   $$\|\mathcal C_1 - \mathcal U_1\|_F \le \varepsilon_1, \qquad \|\mathcal C_2 - \mathcal U_2\|_F \le \varepsilon_2,$$
--   where $\mathcal C_j : \psi\mapsto C_j(\psi\otimes|00\rangle)$ and $\mathcal U_j:\psi\mapsto(U_j\psi)\otimes|00\rangle$. Let $C_2C_1$ be the circuit that runs $C_1$ and then $C_2$. Then
--   $$\|\mathcal{C_2C_1} - \mathcal{U_2U_1}\|_F \le \varepsilon_1 + \varepsilon_2 .$$
--
--   This is the step behind the paper's "the ability to approximate $\Lambda(e^{i\varphi})$ implies the ability to approximate any single qubit unitary": approximations of the factors of a decomposition combine, with the errors added.
--
--   **Formalization Note.** Circuits are lists applied head first, so running $C_1$ and then $C_2$ is the list concatenation `c₁ ++ c₂`, whose matrix is $C_2C_1$. The ancillas of $C_1$ need not be returned clean: any leakage is part of $\varepsilon_1$. Every circuit over $\{H,T,\mathrm{CNOT}\}$ is unitary.
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, p. 2, §2

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-- §2, p. 2: approximations compose. If `c₁` approximates `U₁` (unitary) and `c₂` approximates `U₂`,
with errors measured on the initialized map, then running `c₁` and then `c₂` approximates `U₂ U₁`
with the errors added. -/
theorem composition (c₁ c₂ : Circuit htcxGateSet (1 + 2))
    (U₁ U₂ : Matrix (Qubits 1) (Qubits 1) ℂ) (hU₁ : U₁ ∈ Matrix.unitaryGroup (Qubits 1) ℂ)
    (ε₁ ε₂ : ℝ)
    (h₁ : frobNorm (initializedMap c₁.unitary - idealMap U₁ 2) ≤ ε₁)
    (h₂ : frobNorm (initializedMap c₂.unitary - idealMap U₂ 2) ≤ ε₂) :
    frobNorm (initializedMap (c₁ ++ c₂).unitary - idealMap (U₂ * U₁) 2) ≤ ε₁ + ε₂ := by sorry

end CliffordTApprox.Ancilla
