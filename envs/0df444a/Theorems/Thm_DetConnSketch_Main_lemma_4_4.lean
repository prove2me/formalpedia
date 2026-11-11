-- Prove2me | Theorems.Thm_DetConnSketch_Main_lemma_4_4
-- name    : DetConnSketch.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:06.50339+00:00
-- url     : https://prove2.me/theorems/fc2b7984-3869-4d8a-b110-8863bfcdca78
-- title:
--   Lemma 4.4 — a vertex-cover-forcing sketch $P\in\mathbb F_q^{n\times\tilde O(\sqrt k)}$, $q=\mathrm{poly}(n)$
-- statement:
--   There is a universal constant $C > 0$ such that for all $n$ and $k$ there are a finite field $\mathbb F_q$ with $q \le C(n+2)^C$ and a matrix $P \in \mathbb F_q^{n\times d}$ with $d \le C(\sqrt k + 1)\log^C(n+2)$ with the following property. For every skew-symmetric $M \in \{-1,0,1\}^{n\times n}$ with at most $k$ nonzero entries above its diagonal,
--   $$P^\top M P = 0 \ \Longrightarrow\ \mathrm{Supp}(M) \text{ has a vertex cover of size} \le 10\sqrt k .$$
--
--   In Lemma 4.2, $M = J_S\Delta - \Delta J_S$ encodes the edges crossing a cut; the sketch forces all of them onto few vertices.
--
--   Differences from the source:
--   - reading: P ∈ F_q^{n×Õ(√k)} with q = poly(n) → ∃ C > 0 (before n and k): a finite field F with |F| ≤ C (n+2)^C and P : Matrix (Fin n) (Fin d) F with d ≤ C (√k + 1) (log (n+2))^C; reason: explicit Õ and poly with one universal constant; the shifts n + 2 and √k + 1 only avoid log 1 = 0 and k = 0 and agree with the usual reading for n ≥ 2, k ≥ 1
--   - encoding: parameter k → k : ℕ; reason: for real k ≥ 0, the integer nonzero count is ≤ k iff it is ≤ ⌊k⌋; the conclusion and dimension upper bounds only increase from ⌊k⌋ to k
--   - encoding: skew-symmetric M ∈ {−1,0,1}^{n×n}; Pᵀ M P over F_q → M : Matrix (Fin n) (Fin n) ℤ with M.transpose = −M and entries in {−1,0,1}, cast into F; reason: same matrices
--   - encoding: Supp(M) has a vertex cover of size ≤ 10√k → ∃ U : Finset (Fin n), IsSupportVertexCover M U ∧ |U| ≤ 10√k; reason: same condition
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 23 (PDF 27), Lemma 4.4

import Mathlib
import Definitions.Def_DetConnSketch_Main_SketchMatrices

namespace DetConnSketch.Main

/-- Lemma 4.4 (`Õ(√k)` columns, `q = poly(n)`, with one universal constant `C`): for every `n`
and `k` there are a finite field `F` with `|F| ≤ C (n+2)^C` and `P ∈ F^{n×d}` with
`d ≤ C (√k + 1) (log (n+2))^C` such that every skew-symmetric `M ∈ {−1, 0, 1}^{n×n}` with at
most `k` nonzero entries above its diagonal and `Pᵀ M P = 0` has a support with a vertex cover
of size at most `10√k`. -/
theorem lemma_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ,
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (d : ℕ) (P : Matrix (Fin n) (Fin d) F),
        (Fintype.card F : ℝ) ≤ C * ((n : ℝ) + 2) ^ C ∧
        (d : ℝ) ≤ C * (Real.sqrt k + 1) * Real.log ((n : ℝ) + 2) ^ C ∧
        ∀ M : Matrix (Fin n) (Fin n) ℤ, M.transpose = -M →
          (∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) →
          nnzAboveDiag M ≤ k →
          P.transpose * M.map (Int.cast : ℤ → F) * P = 0 →
          ∃ U : Finset (Fin n), IsSupportVertexCover M U ∧ (U.card : ℝ) ≤ 10 * Real.sqrt k := by sorry

end DetConnSketch.Main
