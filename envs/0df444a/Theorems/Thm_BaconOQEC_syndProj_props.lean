-- Prove2me | Theorems.Thm_BaconOQEC_syndProj_props
-- name    : BaconOQEC.syndProj_props
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:25.144114+00:00
-- url     : https://prove2.me/theorems/d3c21d28-bf61-471f-a10f-57345ccb172d
-- title:
--   Syndrome sectors: orthogonal decomposition, each of dimension $2^{n^2-2(n-1)}$
-- statement:
--   Let $n\ge1$ and for each syndrome $s = (s^X,s^Z)\in\{\pm1\}^{n-1}\times\{\pm1\}^{n-1}$ let $\Pi_s$ be the projector onto the joint eigenspace $\mathcal H_{s^X,s^Z}$ of the stabilizer generators. Then:
--
--   1. each $\Pi_s$ is Hermitian and idempotent;
--   2. $\Pi_s\Pi_{s'} = 0$ for $s\ne s'$, and $\sum_s \Pi_s = I$, the decomposition $\mathcal H = \bigoplus_{s^X,s^Z}\mathcal H_{s^X,s^Z}$ of (14);
--   3. every sector has dimension
--
--   $$
--   \operatorname{tr}\Pi_s = \dim\mathcal H_{s^X,s^Z} = 2^{\,n^2-2(n-1)};
--   $$
--
--   4. the generators act on the sectors by their eigenvalues: $S^X_i\Pi_s = s^X_i\,\Pi_s$ and $S^Z_j\Pi_s = s^Z_j\,\Pi_s$ (15).
--
--   In particular the code sector $\Pi_0$ is nonzero, and every sector holds a $2^{(n-1)^2}$-dimensional gauge subsystem and one encoded qubit.
--
--   Differences from the source:
--   - encoding: lattice size n, rows and columns indexed 1..n, generators indexed by Z_{n−1} → n = m + 1 with m : ℕ; rows and columns Fin (m + 1), 0-based; generators indexed by Fin m acting on i.castSucc, i.succ; reason: Lean convention; n = 0 has no qubits, so every lattice of the paper is an instance
--   - encoding: syndrome eigenvalues s^X_i, s^Z_i = ±1; code sector s^X = s^Z = {+1}^{n−1} → syndrome bits in ZMod 2, bit 0 ↔ eigenvalue +1, bit 1 ↔ −1; code sector s = 0; reason: Lean convention; the same labels
--   - encoding: subspaces H_{s^X,s^Z} and their dimension d → orthogonal projectors Π_s (syndProj s) and their trace; reason: a subspace is the range of its orthogonal projector, whose dimension is its trace
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.B, eqs. (14)–(15), p.6

import Mathlib
import Definitions.Def_BaconOQEC_syndProj

open QAlgorithms
open scoped Matrix

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.B, eqs. (14)–(15), p.6: "We can thus decompose H into subspaces as
H = ⊕_{s^X,s^Z} H_{s^X,s^Z}. By standard arguments in the stabilizer formalism, each of the
H_{s^X,s^Z} subspaces is of dimension d = 2^{n²−2(n−1)}", and "the operators S^X_i and S^Z_i act
under this decomposition as S^X_i = ⊕ s^X_i I, S^Z_i = ⊕ s^Z_i I". For the projectors `Π_s` onto
the syndrome sectors:
1. each `Π_s` is Hermitian and idempotent;
2. `Π_s Π_{s'} = 0` for `s ≠ s'` and `Σ_s Π_s = I` (the orthogonal decomposition (14));
3. `tr Π_s = 2^{n² − 2(n−1)}`, the dimension of `H_{s^X,s^Z}`;
4. `S^X_i Π_s = (−1)^{s^X_i} Π_s` and `S^Z_j Π_s = (−1)^{s^Z_j} Π_s` (15).

**Formalization Note.** `n = m + 1`, so `n² − 2(n − 1) = (m + 1)² − 2m` (no truncation). Syndrome bit
`0` is eigenvalue `+1`, bit `1` is `−1`; `S^X_i`, `S^Z_j` are the matrices `P(SX i)`, `P(SZ j)`. The
dimension of the range of a projector is its trace. -/
theorem syndProj_props (m : ℕ) :
    (∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2), (syndProj s)ᴴ = syndProj s) ∧
    (∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2), syndProj s * syndProj s = syndProj s) ∧
    (∀ s s' : (Fin m → ZMod 2) × (Fin m → ZMod 2), s ≠ s' → syndProj s * syndProj s' = 0) ∧
    (∑ s : (Fin m → ZMod 2) × (Fin m → ZMod 2), syndProj s = 1) ∧
    (∀ s : (Fin m → ZMod 2) × (Fin m → ZMod 2),
      (syndProj s).trace = (2 : ℂ) ^ ((m + 1) ^ 2 - 2 * m)) ∧
    (∀ (s : (Fin m → ZMod 2) × (Fin m → ZMod 2)) (i : Fin m),
      pauliXZ (SX i).1 (SX i).2 * syndProj s = ((-1 : ℂ) ^ (s.1 i).val) • syndProj s) ∧
    (∀ (s : (Fin m → ZMod 2) × (Fin m → ZMod 2)) (j : Fin m),
      pauliXZ (SZ j).1 (SZ j).2 * syndProj s = ((-1 : ℂ) ^ (s.2 j).val) • syndProj s) := by sorry

end BaconOQEC
