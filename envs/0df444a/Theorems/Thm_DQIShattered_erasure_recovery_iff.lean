-- Prove2me | Theorems.Thm_DQIShattered_erasure_recovery_iff
-- name    : DQIShattered.erasure_recovery_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:28.867412+00:00
-- url     : https://prove2.me/theorems/dabfa9b2-9293-4a98-a234-990336109b6b
-- title:
--   §3.2, p.14 — erased bits are recoverable iff $B_S$ has full row rank
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$ and let $S\subseteq\{1,\dots,M\}$ be a set of erased coordinates. The following are equivalent.
--
--   1. The erased bits $(d_j)_{j\in S}$ of every codeword $d\in C^\perp=\{d:B^{\mathsf T}d=0\}$ are uniquely determined by the unerased bits and the parity checks. That is, any two codewords $d,d'\in C^\perp$ that agree outside $S$ are equal.
--   2. The row-submatrix $B_S$, consisting of the rows of $B$ indexed by $S$, has full row rank over $\mathbb F_2$.
--
--   This is the classical step of the USD decoder: after the erasure channel, Gaussian elimination recovers the codeword exactly when $B_S$ has full row rank.
--
--   Differences from the source:
--   - reading: the erased bits are uniquely recoverable from the parity checks Bᵀd = 0 by Gaussian elimination → any two codewords of C^⊥ that agree off S are equal; reason: Gaussian elimination returns the solution of the linear system, which is the codeword exactly when the solution is unique
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), §3.2, p.14

import Mathlib
import Definitions.Def_DQIShattered_Decoding

namespace DQIShattered

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, §3.2, p.14 (erasure recovery).

For every `B ∈ 𝔽₂^{M×N}` and every erased set `S ⊆ {1, …, M}`: the erased bits `(d_j)_{j∈S}` of a codeword
`d ∈ C^⊥` are uniquely determined by the unerased bits and the parity checks `Bᵀd = 0` (any two codewords that
agree off `S` are equal) if and only if the row-submatrix `B_S` has full row rank (its rows are linearly
independent over `𝔽₂`). -/
theorem erasure_recovery_iff {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) :
    (∀ d ∈ dualCode B, ∀ d' ∈ dualCode B, (∀ j, j ∉ S → d j = d' j) → d = d') ↔
      FullRowRankOn B S := by sorry

end DQIShattered
