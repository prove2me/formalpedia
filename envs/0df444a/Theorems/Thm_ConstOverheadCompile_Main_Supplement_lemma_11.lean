-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_Supplement_lemma_11
-- name    : ConstOverheadCompile.Main.Supplement.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:11.886572+00:00
-- url     : https://prove2.me/theorems/b847acaf-5bf9-45de-b6e1-0b51f3e00e39
-- title:
--   Lemma 11 — $\||+^M\rangle-|\phi_{k,M}\rangle\|\le2^{-M/12}$ for $0\le k\le M/4$
-- statement:
--   Let $M\ge1$ be an integer, let $|+^M\rangle$ be the uniform superposition of all $2^M$ basis states of $M$ qubits, and let $|\phi_{k,M}\rangle$ be the (subnormalized) state of Eq. (44): $|\phi_{0,M}\rangle=|+^M\rangle$ and, for $k\ge1$, the sum over $\ell\in\mathbb N_+^k$ with $\sum_j\ell_j\le M$ of $2^{-\sum_j\ell_j/2}|(\ell_1,\dots,\ell_k)\rangle|+^{M-\sum_j\ell_j}\rangle$. Then for every integer $k$ with $0\le k\le M/4$,
--
--   $$\big\||+^M\rangle-|\phi_{k,M}\rangle\big\|\le 2^{-M/12},$$
--
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   The lemma says that for few factors $k$, the uniform superposition $|+^M\rangle$ can stand in for the tuple-encoding state $|\phi_{k,M}\rangle$ in the LCU construction of Theorem 10 (Eq. (50)).
--
--   Differences from the source:
--   - encoding: M ∈ ℕ₊ and 0 ≤ k ≤ M/4 → natural numbers M, k with 1 ≤ M and 4k ≤ M; reason: the same index ranges
--   - encoding: the sum over ℓ ∈ ℕ₊^k with Σℓ_j ≤ M in Eq. (44) → the sum over f : Fin k → Fin M with ℓ_j = f_j + 1 and Σℓ_j ≤ M; reason: every admissible ℓ has ℓ_j ≤ M, so the two index sets are in bijection
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.12, Lemma 11; definitions p.12 Eqs. (43)–(44)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_Supplement_LCU

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Lemma 11, p.12: for every `M ≥ 1` and every `0 ≤ k ≤ M/4`,
`‖|+^M⟩ - |ϕ_{k,M}⟩‖ ≤ 2^{-M/12}` (Euclidean norm on `M` qubits). -/
theorem lemma_11 :
    ∀ M k : ℕ, 1 ≤ M → 4 * k ≤ M →
      ‖plusM M - phiState k M‖ ≤ (2 : ℝ) ^ (-(M : ℝ) / 12) := by sorry

end ConstOverheadCompile.Main.Supplement
