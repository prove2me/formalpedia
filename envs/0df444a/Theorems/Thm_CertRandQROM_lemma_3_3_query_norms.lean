-- Prove2me | Theorems.Thm_CertRandQROM_lemma_3_3_query_norms
-- name    : CertRandQROM.lemma_3_3_query_norms
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:12.234995+00:00
-- url     : https://prove2.me/theorems/a374d158-e505-4879-8b38-0f8c3b0b91d7
-- title:
--   Lemma 3.3 — query norms: unit square sum per query, at most $Q^2/\alpha^2$ heavy inputs
-- statement:
--   Let $\mathcal A$ be a quantum query algorithm making $Q$ queries to an oracle $h$. Then
--
--   1. for every $j\in[Q]$, $\displaystyle\sum_{u}\big(\tilde w^j_u(h)\big)^2=1$;
--   2. for every $\alpha>0$, at most $Q^2/\alpha^2$ inputs $u$ satisfy $\tilde w_u(h)\ge\alpha$:
--
--   $$
--   \#\{u:\tilde w_u(h)\ge\alpha\}\le\frac{Q^2}{\alpha^2}.
--   $$
--
--   Item 2 bounds the number of heavily queried inputs; it is what makes the lists in the list-recovery argument of Claim 7.5 small.
--
--   **Formalization Note** 0-based query index: item 1 is stated for `queryNorm A h j` with $j<Q$, which is the paper's $\tilde w^{j+1}$.
--
--   Differences from the source:
--   - generalization: inputs (i, x) ∈ [n] × Σ → inputs u of any finite type U; reason: taking U = Fin n × Σ gives the paper's statement
--   - encoding: j ∈ [Q], w̃^j uses |ψ_{j−1}⟩ → j < Q, queryNorm A h j uses state j; reason: 0-based index; same values
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ, including Q = 0; reason: for Q ≥ 1 it is the paper's statement; Q = 0 is an extra trivial case
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm

namespace CertRandQROM

/-- **Lemma 3.3** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…), p.15): for any
quantum query algorithm `A` making `Q` queries to an oracle `h`,

1. for every query (0-based `j < Q`, the paper's `j + 1 ∈ [Q]`),
   `Σ_{u} (w̃^{j+1}_u(h))² = 1`;
2. for every `α > 0`, at most `Q²/α²` inputs `u` have `w̃_u(h) ≥ α`.

**Formalization Note** The oracle's input set is any finite type `U` (the paper's
`[n] × Σ`); the query register is exactly `U` (no idle sector), which the equality in item 1
needs. -/
theorem lemma_3_3_query_norms {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h : U → Bool) :
    (∀ j < Q, ∑ u, queryNorm A h j u ^ 2 = 1) ∧
      ∀ α : ℝ, 0 < α →
        ((Finset.univ.filter fun u => α ≤ totalQueryNorm A h u).card : ℝ) ≤ (Q : ℝ) ^ 2 / α ^ 2 := by sorry

end CertRandQROM
