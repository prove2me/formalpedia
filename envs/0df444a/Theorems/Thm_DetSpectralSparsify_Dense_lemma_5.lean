-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_5
-- name    : DetSpectralSparsify.Dense.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:08.808874+00:00
-- url     : https://prove2.me/theorems/592cde6c-dc43-4dcf-a93d-62b243a8fe92
-- title:
--   Lemma 5 (Deterministic matrix Chernoff) — Algorithm 1 selects k ≥ 4Rε⁻² ln(4r) indices with (1±ε)-isotropic average
-- statement:
--   Let $A_1,\dots,A_q$ ($q\ge1$) be positive semidefinite $r\times r$ matrices such that
--   $$\frac1q\sum_{i=1}^qA_i=I,\qquad 0\preceq A_i\preceq RI$$
--   for some $R\ge1$. Let $0<\varepsilon\le1/2$ and let $k$ be a natural number with
--   $$k\ge4R\varepsilon^{-2}\ln(4r). \tag{1}$$
--   Then there are indices $i_1,\dots,i_k\in[q]$, with repetition, such that
--   $$(1-\varepsilon)I\;\preceq\;\frac1k\sum_{j=1}^kA_{i_j}\;\preceq\;(1+\varepsilon)I,$$
--   and every sequence chosen by Algorithm 1 (each $i_j$ minimizing $u_j\langle e^{\theta_+S},A_i\rangle-\ell_j\langle e^{-\theta_-S},A_i\rangle$) has this property.
--
--   This is the deterministic selection step that picks the matchings of the expander sparsifier.
--
--   **Formalization Note** Algorithm 1 is the definition `IsAlg1Selection` (any tie-break). The logarithm is natural. $k$ is any natural number satisfying (1).
--
--   Differences from the source:
--   - encoding: matrices A_1, …, A_q → hypothesis 0 < q; reason: the list notation presumes a nonempty family; for r = 0 the averaging identity alone would not force q ≥ 1
--   - reading: Algorithm 1 finds such indices deterministically → every index sequence satisfying the argmin rule of Algorithm 1, for any tie-break, satisfies the bound; reason: Algorithm 1 says 'choose i_j minimizing'; the statement covers every fixed tie-break
--   - encoding: each iteration evaluates two matrix exponentials and one linear score per candidate → no separate claim; the score in `chernoffScore` is built from the two exponentials and one trace per candidate; reason: the sentence describes the algorithm's operations, which the definition already fixes
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.6, Lemma 5 and Algorithm 1

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph
import Definitions.Def_DetSpectralSparsify_Dense_MatrixChernoff

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 5 (Deterministic matrix Chernoff), p.6. For PSD `r × r` matrices with
`(1/q) ∑ A_i = I`, `0 ⪯ A_i ⪯ R I`, `R ≥ 1`, `0 < ε ≤ 1/2` and `k ≥ 4 R ε⁻² ln(4r)`, there are
indices `i_1, …, i_k` (with repetition) such that `(1-ε) I ⪯ (1/k) ∑_j A_{i_j} ⪯ (1+ε) I`, and
every sequence chosen by Algorithm 1 is such a sequence. -/
theorem lemma_5 {r q k : ℕ} (A : Fin q → Matrix (Fin r) (Fin r) ℝ) (R ε : ℝ)
    (hq : 0 < q) (hA : ∀ i, (A i).PosSemidef) (hAR : ∀ i, PSDLe (A i) (R • 1))
    (havg : (q : ℝ)⁻¹ • ∑ i, A i = 1) (hR : 1 ≤ R) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hk : 4 * R * (ε ^ 2)⁻¹ * Real.log (4 * r) ≤ k) :
    (∃ idx : Fin k → Fin q,
      PSDLe ((1 - ε) • (1 : Matrix (Fin r) (Fin r) ℝ)) ((k : ℝ)⁻¹ • ∑ j, A (idx j)) ∧
      PSDLe ((k : ℝ)⁻¹ • ∑ j, A (idx j)) ((1 + ε) • (1 : Matrix (Fin r) (Fin r) ℝ))) ∧
    ∀ idx : Fin k → Fin q, IsAlg1Selection A R ε idx →
      PSDLe ((1 - ε) • (1 : Matrix (Fin r) (Fin r) ℝ)) ((k : ℝ)⁻¹ • ∑ j, A (idx j)) ∧
      PSDLe ((k : ℝ)⁻¹ • ∑ j, A (idx j)) ((1 + ε) • (1 : Matrix (Fin r) (Fin r) ℝ)) := by sorry

end DetSpectralSparsify.Dense
