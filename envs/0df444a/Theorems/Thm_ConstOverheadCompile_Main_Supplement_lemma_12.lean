-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_Supplement_lemma_12
-- name    : ConstOverheadCompile.Main.Supplement.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:48.730318+00:00
-- url     : https://prove2.me/theorems/d1dc6eba-bfa2-438e-841c-721bbb8f0360
-- title:
--   Lemma 12 (PREPARE lemma) — for $c$ large, $O(n)$ gates over $\{H,T,\mathrm{CNOT}\}$ on $B=O(n)$ qubits prepare $\sum_k\sqrt{\alpha_k}|k\rangle|g_k\rangle$ to within $2^{-4n}$
-- statement:
--   Let $c$ be the constant of Eq. (46) and, for $n\ge1$, let $K=\lceil cn/\log_2(n+2)\rceil$, $\Lambda_K=\sum_{k=0}^K\pi^k/k!$ and $\alpha_k=\pi^k/(\Lambda_Kk!)$. Let $r=\lceil\log_2(K+1)\rceil$ and write $|k\rangle$ for $k$ in binary on $r$ qubits.
--
--   There is a threshold $c_0$ such that for every $c\ge c_0$ there is a constant $C$ (depending only on $c$) with the following property. For every $n\ge1$ there are an integer $B'$, a unitary circuit $\mathrm{PREP}_n$ over $\mathcal G=\{H,T,\mathrm{CNOT}\}$ acting on $B=r+B'$ qubits, with
--
--   1. $B\le Cn$ and at most $Cn$ gates, and
--   2. unit vectors $|g_0\rangle,\dots,|g_K\rangle$ on $B'$ qubits,
--
--   such that
--
--   $$\Big\|\mathrm{PREP}_n|0^B\rangle-\sum_{k=0}^K\sqrt{\alpha_k}\,|k\rangle|g_k\rangle\Big\|\le2^{-4n}.$$
--
--   This is the PREPARE step of the linear-combination-of-unitaries construction of Theorem 10: it loads the truncated Taylor weights of $e^{-iH}$ into a register, with arbitrary normalized garbage $|g_k\rangle$.
--
--   Differences from the source:
--   - encoding: c in Eq. (46) a sufficiently large constant → ∃ c₀, ∀ c ≥ c₀, ∃ C (C quantified after c, before n); reason: the meaning of 'sufficiently large'; the O(n) constants may depend on c, which is fixed, but not on n
--   - encoding: O(n) gates and B = O(n) ancillas → size ≤ C·n and total width B = r + B' ≤ C·n; reason: PREP_n acts on the B-qubit register |0^B⟩ (Eqs. (48)–(49))
--   - reading: |k⟩ in a register of PREP_n's output → k in binary (most significant bit first) on the first r = ⌈log₂(K+1)⌉ wires, |g_k⟩ on the remaining B' wires; reason: the source does not fix the layout; Eq. (51) (two bits determine (−i)^k) and the register size of SELECT on p.13 show the binary register of ⌈log₂(K+1)⌉ qubits; bit order is a relabeling of wires
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.13, Lemma 12, Eq. (48); K, Λ_K, α_k: p.12 Eq. (46); proof: Appendix C.2, pp.22–25

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_Supplement_LCU

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Lemma 12 (PREPARE lemma), p.13: there is `c₀` such that for every constant `c ≥ c₀` in
Eq. (46) there is `C` with the following property. For every `n ≥ 1`, with `K = ⌈c n / log₂(n+2)⌉`
and `r = ⌈log₂(K + 1)⌉`, there are a unitary circuit `PREP_n` over `𝒢 = {H, T, CNOT}` on
`B = r + B'` qubits, with `B ≤ C n` and at most `C n` gates, and unit vectors `|g_k⟩` on `B'`
qubits (`0 ≤ k ≤ K`), such that
`‖PREP_n |0^B⟩ - Σ_{k=0}^{K} √α_k |k⟩|g_k⟩‖ ≤ 2^{-4n}`, `|k⟩` written in binary on the first `r`
wires. -/
theorem lemma_12 :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ (B' : ℕ) (U : Circuit CliffordT (kWidth (taylorK c n) + B'))
        (g : Fin (taylorK c n + 1) → EuclideanSpace ℂ (Qubits B')),
        (((kWidth (taylorK c n) + B' : ℕ) : ℝ) ≤ C * n) ∧
        (U.size : ℝ) ≤ C * n ∧
        (∀ k, ‖g k‖ = 1) ∧
        ‖act U.unitary (zeroKet (kWidth (taylorK c n) + B')) -
            ∑ k : Fin (taylorK c n + 1),
              ((Real.sqrt (alphaK (taylorK c n) k) : ℝ) : ℂ) •
                kTensor (kWidth (taylorK c n)) k (g k)‖ ≤ ((1 : ℝ) / 2) ^ (4 * n) := by sorry

end ConstOverheadCompile.Main.Supplement
