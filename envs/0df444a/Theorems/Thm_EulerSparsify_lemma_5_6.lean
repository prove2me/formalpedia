-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_6
-- name    : EulerSparsify.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:26.733702+00:00
-- url     : https://prove2.me/theorems/75a0cec1-3baa-4170-90bf-a4f2b8f6f003
-- title:
--   Lemma 5.6 — $PP^\top\preceq QQ^\top$ implies $\sum_i\tilde A_i\tilde A_i^\top\preceq\sum_i\hat A_i\hat A_i^\top$
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb R^{n\times n}$ and let $P,Q\in\mathbb R^{m\times m}$ satisfy $PP^\top\preceq QQ^\top$. For $i\in[m]$ put $\tilde A_i=\sum_{j\in[m]}P_{ji}A_j$ and $\hat A_i=\sum_{j\in[m]}Q_{ji}A_j$. Then
--
--   $$\sum_{i\in[m]}\tilde A_i\tilde A_i^\top\ \preceq\ \sum_{i\in[m]}\hat A_i\hat A_i^\top .$$
--
--   Mixing a family of matrices by a Loewner-smaller matrix can only decrease its matrix variance; Lemma 5.9 uses it to pass from $R$ to the projection $P_S$.
--
--   Differences from the source: none.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.6, p.18 (PDF p.20)

import Mathlib

namespace EulerSparsify

/-- **Lemma 5.6**, p.18, PDF p.20.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.6: "Let {A_i}_{i∈[m]} ∈ ℝ^{n×n} and let P, Q ∈ ℝ^{m×m} be matrices such that
PPᵀ ≼ QQᵀ. For each i ∈ [m], let Ã_i := Σ_{j∈[m]} P_ji A_j and Â_i := Σ_{j∈[m]} Q_ji A_j. Then,
Σ_{i∈[m]} Ã_i Ã_iᵀ ⪯ Σ_{i∈[m]} Â_i Â_iᵀ."

**Formalization Note.** `X ≼ Y` is `(Y − X).PosSemidef`. Indices `[m]`, `[n]` are `Fin m`,
`Fin n`. -/
theorem lemma_5_6 {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (P Q : Matrix (Fin m) (Fin m) ℝ) (hPQ : (Q * Q.transpose - P * P.transpose).PosSemidef) :
    ((∑ i, (∑ j, Q j i • A j) * (∑ j, Q j i • A j).transpose) -
      ∑ i, (∑ j, P j i • A j) * (∑ j, P j i • A j).transpose).PosSemidef := by sorry

end EulerSparsify
