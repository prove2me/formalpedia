-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_Supplement_theorem_3
-- name    : ConstOverheadCompile.Main.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:32:41.133451+00:00
-- url     : https://prove2.me/theorems/7a2981d9-8c18-4a49-9a1e-c42d14ebc481
-- title:
--   Theorem 3 (optimal phase gradient state preparation) — a unitary $\{H,T,\mathrm{CNOT}\}$ circuit of $O(n)$ gates prepares $|\mathrm{grad}_n\rangle$ to within $2^{-n}$
-- statement:
--   Let $|\mathrm{grad}_n\rangle=\bigotimes_{j=0}^{n-1}R(\pi/2^j)|+\rangle$ be the phase gradient state of Eq. (6), with $R(\theta)=\mathrm{diag}(1,e^{i\theta})$.
--
--   There is a constant $C$ such that for every $n\ge1$ there are an integer $a\ge0$, a unitary circuit $U$ over $\mathcal G=\{H,T,\mathrm{CNOT}\}$ on $n+a$ qubits with at most $Cn$ gates, and a real phase $\varphi$, such that
--
--   $$\big\|\,U|0^{n+a}\rangle-e^{i\varphi}\,|\mathrm{grad}_n\rangle\otimes|0^a\rangle\big\|\le2^{-n},$$
--
--   with the data on the first $n$ wires and every ancilla returned (approximately) to $|0\rangle$; $\|\cdot\|$ is the Euclidean norm on $n+a$ qubits. No measurements are used.
--
--   Preparing $|\mathrm{grad}_n\rangle$ naively costs $n$ arbitrary $Z$-rotations, each needing $\Theta(\log(1/\epsilon))$ gates; the theorem removes the logarithmic factor (and the adaptivity and expected-cost bound of Jones' construction). In the paper it supplies the resource states of the compilation of Theorem 2.
--
--   Differences from the source:
--   - reading: prepares |grad_n⟩ to within error 2^{−n} → Euclidean distance at most 2^{−n} between the whole (n + a)-qubit output U|0^{n+a}⟩ and e^{iφ}|grad_n⟩ ⊗ |0^a⟩ for some real φ; reason: the error measure is not specified; the paper identifies states up to global phase (p.4 and p.11: 'Up to a global phase, this agrees with our definition in Eq. (6)', and its proof prepares (γ/|γ|)|grad_n⟩, Eq. (41)), while returning the ancillas to |0⟩ is the stronger of the readings about workspace and is what the proof delivers
--   - encoding: a unitary circuit, ancillas not mentioned → a circuit on n + a wires for some a, the ancillas starting in |0⟩; reason: the proof uses a = O(n) ancillas; their number is not bounded by the theorem, only the gates
--   - encoding: O(n) gates → one constant C quantified before n, size ≤ C·n; reason: meaning of the bound
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.3, Theorem 3, Eq. (6); proof: p.11–12 (from Theorem 10)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_Supplement_PhaseGradient

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Theorem 3, p.3: there is a constant `C` such that for every `n ≥ 1` some unitary circuit over
`𝒢 = {H, T, CNOT}` on `n + a` wires, started in `|0^{n+a}⟩`, with at most `C n` gates, outputs a
vector within Euclidean distance `2^{-n}` of `e^{iφ} |grad_n⟩ ⊗ |0^a⟩` for some global phase `φ`
(data on wires `0, …, n - 1`, ancillas returned to `|0⟩`). -/
theorem theorem_3 :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ (a : ℕ) (U : Circuit CliffordT (n + a)) (φ : ℝ),
        (U.size : ℝ) ≤ C * n ∧
        ‖act U.unitary (zeroKet (n + a)) -
            Complex.exp ((φ : ℂ) * Complex.I) • padZero a (gradState n)‖ ≤ ((1 : ℝ) / 2) ^ n := by sorry

end ConstOverheadCompile.Main.Supplement
