-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_ross_selinger_synthesis
-- name    : ConstOverheadCompile.Main.ross_selinger_synthesis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:45.483131+00:00
-- url     : https://prove2.me/theorems/b81bb7ad-ec2a-43e0-a603-8db2c21dbc18
-- title:
--   §1, p.1 [RS16]: every one- or two-qubit gate to error $\epsilon$ with $O(\log(1/\epsilon))$ gates over $\{H,T,\mathrm{CNOT}\}$, no ancillas
-- statement:
--   There are constants $C>0$ and $\varepsilon_0>0$ with the following property. For every $\varepsilon\in(0,\varepsilon_0)$, every $k\in\{1,2\}$ and every unitary $U$ on $k$ qubits there is a circuit $c$ over $\mathcal G=\{H,T,\mathrm{CNOT}\}$ on the same $k$ wires (no ancillas) with
--   $$|c|\le C\log(1/\varepsilon)\qquad\text{and}\qquad \min_{\varphi\in\mathbb R}\big\|U-e^{i\varphi}U_c\big\|\le\varepsilon ,$$
--   where $\|\cdot\|$ is the spectral (operator) norm.
--
--   The paper cites this result of Ross and Selinger as the standard per-gate synthesis cost; it is the tool with which the resource states are prepared in the proofs of Theorems 7 and 9.
--
--   Differences from the source:
--   - reading: "to within error ε" → spectral-norm distance up to a global phase; reason: the standard error measure of gate synthesis; a phase must be allowed because products of $H$, $T$ and CNOT have determinants in a finite group and cannot approximate every phase of $U$.
--   - encoding: $O(\log(1/\varepsilon))$ → constants $C,\varepsilon_0>0$ quantified before $\varepsilon$, $k$, $U$ with the bound for all $\varepsilon<\varepsilon_0$; reason: the literal meaning of the asymptotic as $\varepsilon\to0$.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.1, §1 (citing [RS16]: N. J. Ross, P. Selinger, Optimal ancilla-free Clifford+T approximation of z-rotations, QIC 16(11–12), 2016)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- §1, p.1, citing [RS16]: there are constants `C, ε₀ > 0` such that for every `ε ∈ (0, ε₀)`,
every unitary `U` on one or on two qubits is approximated to spectral-norm error `ε`, up to a
global phase, by a circuit over `{H, T, CNOT}` on the same wires (no ancillas) with at most
`C log(1/ε)` gates. -/
theorem ross_selinger_synthesis :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ k : ℕ, (k = 1 ∨ k = 2) →
        ∀ U : Matrix (Qubits k) (Qubits k) ℂ, U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
          ∃ c : Circuit CliffordT k,
            (c.size : ℝ) ≤ C * Real.log (1 / ε) ∧ ApproxUpToPhase U c.unitary ε := by sorry

end ConstOverheadCompile.Main
