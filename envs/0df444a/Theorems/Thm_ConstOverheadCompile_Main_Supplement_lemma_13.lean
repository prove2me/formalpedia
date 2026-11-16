-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_Supplement_lemma_13
-- name    : ConstOverheadCompile.Main.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:20.624209+00:00
-- url     : https://prove2.me/theorems/bd1bfb16-1a7c-478c-a7ad-1848d22d842d
-- title:
--   Lemma 13 (SELECT lemma) — for $K\le M/4$, $M=\Theta(n)$, SELECT of Eq. (53) exactly with $O(M)$ gates over $\{H,T,\mathrm{CNOT}\}$ and $O(M)$ ancillas
-- statement:
--   Let $n\ge1$, $M$ and $K$ be integers with $K\le M/4$ and $M=\Theta(n)$, and let $r=\lceil\log_2(K+1)\rceil$. For $\ell\in\mathbb N_+$ let $P_\ell$ be the Pauli $Z$ on the $\ell$-th of $n$ data qubits if $\ell\le n$, and the identity otherwise (Eq. (54)).
--
--   For every $\kappa\ge1$ there is a constant $C$ such that whenever $n\le\kappa M$, $M\le\kappa n$ and $4K\le M$, there are $b\le CM$ and a unitary circuit SELECT over $\mathcal G=\{H,T,\mathrm{CNOT}\}$ on $r+M+n+b$ qubits with at most $CM$ gates such that, for every $0\le k\le K$, every $(\ell_1,\dots,\ell_k)\in\mathbb N_+^k$ with $\sum_j\ell_j\le M$ and every vector $|\phi\rangle$ on $n$ qubits,
--
--   $$\mathrm{SELECT}\,|k\rangle|(\ell_1,\dots,\ell_k)\rangle|+^{M-\sum_j\ell_j}\rangle|\phi\rangle|0^b\rangle=|k\rangle|(\ell_1,\dots,\ell_k)\rangle|+^{M-\sum_j\ell_j}\rangle\Big(\prod_{j=1}^kP_{\ell_j}\Big)|\phi\rangle|0^b\rangle,$$
--
--   exactly. Here $|k\rangle$ is $k$ in binary on $r$ qubits and $|(\ell_1,\dots,\ell_k)\rangle$ is the tuple encoding of Eq. (43). On inputs not of this form SELECT is unconstrained.
--
--   This is the SELECT step of the linear-combination-of-unitaries construction of Theorem 10: from the encoded tuple it applies the product of Pauli $Z$ operators selected by the gaps $\ell_j$.
--
--   Differences from the source:
--   - reading: M = Θ(n) → for every κ ≥ 1, the constant C serves all n, M with n ≤ κM and M ≤ κn; reason: the standard meaning of Θ with the hidden constants fixed; C depends only on κ
--   - reading: O(M) gates from 𝒢 and ancillas → both the gate count and the number b of ancillas are at most C·M; reason: the sentence bounds both; the stronger of the two parsings
--   - reading: a unitary SELECT acting as in Eq. (53), implemented using ancillas → the ancillas start in |0^b⟩ and are returned to |0^b⟩ on every input of the form (53); reason: otherwise the circuit does not act as Eq. (53) on the r + M + n qubits; the proof uncomputes all auxiliary data (Appendix C.1)
--   - encoding: |ϕ⟩ any n-qubit state → any vector ϕ on n qubits; reason: both sides are linear in ϕ, and every vector is a scalar multiple of a state, so the two statements are equivalent
--   - encoding: K ≤ M/4; registers |k⟩|(ℓ)⟩|+^{M−Σℓ_j}⟩|ϕ⟩ → 4K ≤ M; wires in the order k-register (r, binary, most significant bit first), M-register, data, ancillas; reason: the same condition; the wire order is a relabeling, free since gates act on any wires
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.13, Lemma 13 and Eqs. (53)–(54); proof: Appendix C.1, pp.18–22

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_Supplement_LCU

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Lemma 13 (SELECT lemma), p.13, with `M = Θ(n)` read as `n ≤ κ M` and `M ≤ κ n`: for every
`κ ≥ 1` there is `C` such that for all `n ≥ 1`, `M`, `K` with `n ≤ κ M`, `M ≤ κ n` and
`K ≤ M/4`, with `r = ⌈log₂(K + 1)⌉`, some unitary circuit over `𝒢 = {H, T, CNOT}` on
`r + M + n + b` wires with at most `C M` gates and `b ≤ C M` ancillas satisfies, exactly, for every
`0 ≤ k ≤ K`, every `ℓ ∈ ℕ₊^k` with `Σ_j ℓ_j ≤ M` and every `n`-qubit vector `ϕ`,
`SELECT |k⟩|(ℓ)⟩|+^{M - Σ ℓ_j}⟩|ϕ⟩|0^b⟩ = |k⟩|(ℓ)⟩|+^{M - Σ ℓ_j}⟩ (∏_j P_{ℓ_j}) |ϕ⟩|0^b⟩`. -/
theorem lemma_13 :
    ∀ κ : ℝ, 1 ≤ κ → ∃ C : ℝ, ∀ n M K : ℕ, 1 ≤ n → (n : ℝ) ≤ κ * M → (M : ℝ) ≤ κ * n →
      4 * K ≤ M →
        ∃ (b : ℕ) (U : Circuit CliffordT (kWidth K + M + n + b)),
          (U.size : ℝ) ≤ C * M ∧ (b : ℝ) ≤ C * M ∧
          ∀ k : ℕ, k ≤ K → ∀ ℓ : Fin k → ℕ+, tupleLen ℓ ≤ M →
            ∀ ϕ : EuclideanSpace ℂ (Qubits n),
              act U.unitary (selectState (kWidth K) M n b k ℓ ϕ) =
                selectState (kWidth K) M n b k ℓ (act (selProd n ℓ) ϕ) := by sorry

end ConstOverheadCompile.Main.Supplement
