-- Prove2me | Theorems.Thm_CertRandQROM_lemma_4_1_local_stability
-- name    : CertRandQROM.lemma_4_1_local_stability
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:47.752183+00:00
-- url     : https://prove2.me/theorems/ad3f5084-35db-437a-8452-4d05cbd67b60
-- title:
--   Lemma 4.1 (Local Stability of Query Norms)
-- statement:
--   Let $h,h'$ be oracles and $X$ the set of inputs on which they differ. For every $j\in[Q]$ and every input $u$,
--
--   $$
--   \big|\tilde w^j_u(h)-\tilde w^j_u(h')\big|\le 2\sum_{j'<j}\ \sum_{u'\in X}\tilde w^{j'}_{u'}(h).
--   $$
--
--   Query norms are themselves stable: changing the oracle on lightly queried inputs barely changes the query norm of any input.
--
--   **Formalization Note** 0-based: the paper's query $j\in[Q]$ is $j+1$ here; `queryNorm A h j` is $\tilde w^{j+1}$, and the paper's $1\le j'<j+1$ is $j'<j$.
--
--   Differences from the source:
--   - generalization: inputs (i, x) ∈ [n] × Σ → inputs u of any finite type U; reason: taking U = Fin n × Σ gives the paper's statement
--   - encoding: j ∈ [Q], Σ_{j'<j} w̃^{j'} → j < Q, Σ_{j' < j} queryNorm A h j'; reason: 0-based index; same values
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ, including Q = 0; reason: for Q ≥ 1 it is the paper's statement; Q = 0 is an extra trivial case
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 4.1 (Local Stability of Query Norms), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm

namespace CertRandQROM

/-- **Lemma 4.1 (Local Stability of Query Norms)** (Coladangelo et al., arXiv:2608.31112
(sha256 b75095a2…), p.17): let `X` be the set of inputs on which the oracles `h, h'` differ.
For every query and every input `u`,
`|w̃^j_u(h) − w̃^j_u(h')| ≤ 2 Σ_{j' < j} Σ_{u' ∈ X} w̃^{j'}_{u'}(h)`.

**Formalization Note** 0-based: the paper's `j ∈ [Q]` is `j + 1` here, `w̃^{j+1}` is
`queryNorm A · j`, and the paper's `j' < j + 1`, `j' ≥ 1` become `j' < j`. -/
theorem lemma_4_1_local_stability {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h h' : U → Bool) (j : ℕ)
    (hj : j < Q) (u : U) :
    |queryNorm A h j u - queryNorm A h' j u| ≤
      2 * ∑ j' ∈ Finset.range j,
        ∑ u' ∈ Finset.univ.filter (fun u' => h u' ≠ h' u'), queryNorm A h j' u' := by sorry

end CertRandQROM
