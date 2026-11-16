-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_Supplement_theorem_10
-- name    : ConstOverheadCompile.Main.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:54.199574+00:00
-- url     : https://prove2.me/theorems/c6d69e8e-fcc8-4fbf-8a73-30c718a8afd6
-- title:
--   Theorem 10 (heralded approximate state preparation) — $(I\otimes\langle0^a|)W|0^{n+a}\rangle=\gamma|\mathrm{grad}_n\rangle+|E\rangle$, $|\gamma|\ge0.01$, $\|E\|\le2^{-2n}$
-- statement:
--   Let $c$ be the constant of Eq. (46). For $n\ge1$ let $K=\lceil cn/\log_2(n+2)\rceil$, $\Lambda_K=\sum_{k=0}^K\pi^k/k!$ and
--   $$\gamma=\frac{e^{-i\pi2^{-n}}}{\Lambda_K}\qquad\text{(Eq. (63))},$$
--   and let $|\mathrm{grad}_n\rangle=e^{-iH}|+^n\rangle$ with $H=\pi\sum_{j=1}^n2^{-j}Z_j$ (Eq. (36)).
--
--   There is a threshold $c_0$ such that for every $c\ge c_0$ there is a constant $C$ with the following property. For every $n\ge1$ there are $a\le Cn$ and a unitary circuit $W$ over $\mathcal G=\{H,T,\mathrm{CNOT}\}$ on $n+a$ qubits with at most $Cn$ gates such that
--
--   $$(I\otimes\langle0^a|)\,W|0^{n+a}\rangle=\gamma|\mathrm{grad}_n\rangle+|E\rangle,\qquad \||E\rangle\|\le2^{-2n},$$
--
--   and $|\gamma|\ge0.01$. Here $(I\otimes\langle0^a|)$ keeps the component in which all $a$ ancillas are $|0\rangle$ (no renormalization), so the left side is a subnormalized $n$-qubit vector.
--
--   Theorem 10 is a heralded preparation of the phase gradient state with known success amplitude $\gamma$; the paper derives Theorem 3 from it by a constant number of rounds of exact amplitude amplification.
--
--   Differences from the source:
--   - encoding: c in Eq. (46) a sufficiently large absolute constant → ∃ c₀, ∀ c ≥ c₀, ∃ C (C quantified after c, before n); γ = γ(c, n) explicit; reason: the meaning of 'sufficiently large'; γ depends on c through K, and the O(n) constants may depend on the fixed c but not on n
--   - encoding: O(n) gates and a = O(n) ancillas → size ≤ C·n and a ≤ C·n; reason: meaning of the bounds
--   - encoding: |grad_n⟩ in Eq. (37) → gradExp n, the vector e^{−iH}|+^n⟩ of Eq. (36); reason: §5 writes |grad_n⟩ for Eq. (36), and the explicit γ refers to that vector
--   - encoding: W on registers with the data register last (Eq. (64)) → data on wires 0, …, n−1, ancillas on wires n, …, n+a−1; reason: a relabeling of wires, free since gates act on any wires
--   - encoding: |E⟩ an n-qubit state with ‖|E⟩‖ ≤ 2^{−2n} → the norm of the difference (I ⊗ ⟨0^a|)W|0^{n+a}⟩ − γ|grad_n⟩ is at most 2^{−2n}; reason: |E⟩ is defined by Eq. (37) as that difference; it is not normalized
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.11, Theorem 10, Eq. (37); γ: p.14 Eq. (63); K, Λ_K: p.12 Eq. (46); |grad_n⟩: p.11 Eq. (36); proof pp.12–14

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_Supplement_PhaseGradient
import Definitions.Def_ConstOverheadCompile_Main_Supplement_LCU

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Theorem 10 (heralded approximate state preparation), p.11: there is `c₀` such that for every
constant `c ≥ c₀` in Eq. (46) there is `C` with the following property. For every `n ≥ 1` some
unitary circuit `W` over `𝒢 = {H, T, CNOT}` on `n + a` wires, with `a ≤ C n` ancillas and at most
`C n` gates, satisfies `(I ⊗ ⟨0^a|) W |0^{n+a}⟩ = γ |grad_n⟩ + |E⟩` with `‖E‖ ≤ 2^{-2n}`, where
`|grad_n⟩ = e^{-iH}|+^n⟩` (Eq. (36)) and `γ = e^{-iπ 2^{-n}} / Λ_K` (Eq. (63)) satisfies
`|γ| ≥ 0.01`. -/
theorem theorem_10 :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ (a : ℕ) (W : Circuit CliffordT (n + a)),
        (a : ℝ) ≤ C * n ∧ (W.size : ℝ) ≤ C * n ∧
        (0.01 : ℝ) ≤ ‖gammaC c n‖ ∧
        ‖projZero (act W.unitary (zeroKet (n + a))) - gammaC c n • gradExp n‖ ≤
          ((1 : ℝ) / 2) ^ (2 * n) := by sorry

end ConstOverheadCompile.Main.Supplement
