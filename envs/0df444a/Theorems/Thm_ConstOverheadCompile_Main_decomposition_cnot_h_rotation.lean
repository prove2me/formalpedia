-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_decomposition_cnot_h_rotation
-- name    : ConstOverheadCompile.Main.decomposition_cnot_h_rotation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:41.659198+00:00
-- url     : https://prove2.me/theorems/e5afad5a-f577-49fd-8fb9-e142802f8d1a
-- title:
--   §1, p.4: every one- or two-qubit gate is a product of a constant number of CNOT, $H$ and $R(\theta)$ gates
-- statement:
--   There is a constant $N$ with the following property. Let $k\in\{1,2\}$ and let $U$ be any unitary on $k$ qubits. Then there is a circuit $c$ on the same $k$ wires, each of whose gates is a CNOT, a Hadamard $H$, or a Z-rotation $R(\theta)$ with $\theta\in(0,2\pi)$, such that
--   $$|c|\le N\qquad\text{and}\qquad U=U_{c},$$
--   where $U_c$ is the unitary implemented by $c$. The equality is exact, with no global phase.
--
--   This is the reduction with which the proofs of Theorem 7 and Theorem 1 begin: the input circuit may be assumed to consist of CNOT, $H$ and Z-rotations at a constant-factor cost.
--
--   Differences from the source:
--   - encoding: "a constant number of such gates" → one natural number $N$ quantified before $k$ and $U$; reason: this is the meaning of "constant".
--   - encoding: "any one- or two-qubit gate" → any unitary matrix on one or on two qubits, decomposed on the same wires; reason: no ancillas are mentioned, and on one wire CNOT cannot be placed.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.4, §1 "Proof overview of Theorem 1" (decomposition claim); also p.10, §4

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- §1, p.4: there is one constant `N` such that every unitary on one or on two qubits equals,
exactly (no global phase), the unitary of a circuit on the same wires with at most `N` gates,
each a CNOT, an `H` or a rotation `R(θ)` with `θ ∈ (0, 2π)`. -/
theorem decomposition_cnot_h_rotation :
    ∃ N : ℕ, ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ, U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U := by sorry

end ConstOverheadCompile.Main
