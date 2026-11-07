-- Prove2me | Theorems.Thm_CertRandQROM_lemma_3_4_swapping
-- name    : CertRandQROM.lemma_3_4_swapping
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:14.615261+00:00
-- url     : https://prove2.me/theorems/ecba0866-9cd2-458e-b2ca-1351c0635fc1
-- title:
--   Lemma 3.4 (Swapping Lemma) — states under two oracles differ by at most twice the query norm on the difference set
-- statement:
--   Let $h,h'$ be oracles and $X$ the set of inputs on which they differ. For every $j\in[Q]$,
--
--   $$
--   \big\||\psi^h_j\rangle-|\psi^{h'}_j\rangle\big\|_2\le 2\sum_{j'=1}^{j}\ \sum_{u\in X}\tilde w^{j'}_u(h).
--   $$
--
--   The swapping lemma is the basic tool for comparing an adversary's runs on oracles that differ on few, lightly queried inputs; it is adapted from Ambainis et al. and Bennett–Bernstein–Brassard–Vazirani.
--
--   **Formalization Note** 0-based: $\tilde w^{j'}_u(h)$ for $j'=1,\dots,j$ is `queryNorm A h (j'-1) u`, so the sum runs over $j'<j$. The statement is for every $j\le Q$; $j=0$ is the trivial case.
--
--   Differences from the source:
--   - generalization: inputs (i, x) ∈ [n] × Σ → inputs u of any finite type U; reason: taking U = Fin n × Σ gives the paper's statement
--   - encoding: Σ_{j'=1}^{j} w̃^{j'} → Σ_{j' < j} queryNorm A h j'; reason: 0-based index; same values
--   - generalization: j ∈ [Q] → j ≤ Q (adds j = 0); reason: at j = 0 both sides are 0
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ, including Q = 0; reason: for Q ≥ 1 it is the paper's statement; Q = 0 is an extra trivial case
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 3.4 (Swapping Lemma), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm

namespace CertRandQROM

/-- **Lemma 3.4 (Swapping Lemma)** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…),
p.16; adapted from [EJPV98, Lemma 2], [BBBV97, Theorem 3.3]): let `X` be the set of inputs on
which the oracles `h, h'` differ. Then after `j` queries
`‖|ψ_j^h⟩ − |ψ_j^{h'}⟩‖₂ ≤ 2 Σ_{j'=1}^{j} Σ_{u ∈ X} w̃^{j'}_u(h)`.

**Formalization Note** 0-based query norms: the paper's `w̃^{j'}_u(h)` (`j' = 1, …, j`) is
`queryNorm A h (j' − 1) u`, so the sum is over `j' < j`. The statement is for every `j ≤ Q`
(`j = 0` is the trivial case `0 ≤ 0`). -/
theorem lemma_3_4_swapping {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h h' : U → Bool) (j : ℕ)
    (hj : j ≤ Q) :
    ‖A.state h j - A.state h' j‖ ≤
      2 * ∑ j' ∈ Finset.range j,
        ∑ u ∈ Finset.univ.filter (fun u => h u ≠ h' u), queryNorm A h j' u := by sorry

end CertRandQROM
