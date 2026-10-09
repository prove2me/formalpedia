-- Prove2me | Theorems.Thm_DiazModulus_candidate_two_by_two_config_entry_not_mem_span_logAlg
-- name    : DiazModulus.candidate_two_by_two_config_entry_not_mem_span_logAlg
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:09:42.965557+00:00
-- url     : https://prove2.me/theorems/b75876be-a526-429b-b5a6-8efe1b704206
-- title:
--   At a candidate u with u, w₁…w_m algebraically independent over Q̄, every 2×2 configuration in Q̄ + Q̄u + Q̄ū + ΣQ̄w_k has, in every row and every column, an entry outside the Q̄-span of the logarithms
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`) with $u, w_1, \dots, w_m$ algebraically independent over $\overline{\mathbb{Q}}$. For every $2 \times 2$ configuration $x, y$ over $\overline{\mathbb{Q}}$ in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}w_1 + \dots + \overline{\mathbb{Q}}w_m$, each row and each column of $(x_iy_j)$ contains an entry outside $\overline{\mathbb{Q}}\,\mathcal{L}$. In particular the matrix is never a matrix of logarithms of algebraic numbers, so the four exponentials theorem can never be applied to it. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** $u\bar u = |u|^2$ is algebraic, so `DiazModulus.circle_point_config_constant_matrix_det_ne_zero` with $K = \overline{\mathbb{Q}}$ gives an invertible $c$ with $x_iy_j - c_{ij} \in \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$; every row and column of $c$ has a non-zero entry. Since $u, \bar u \in \mathcal{L}$ (`DiazModulus.logAlg_conj_stable`), $x_iy_j \in \overline{\mathbb{Q}}\,\mathcal{L}$ would put the algebraic number $c_{ij}$ in $\overline{\mathbb{Q}}\,\mathcal{L}$, and `DiazModulus.algebraic_mem_span_logAlg_eq_zero` would give $c_{ij} = 0$.
--
--   **Novelty.** Not found in the sources read; it is short: the invertible constant matrix (`DiazModulus.circle_point_config_constant_matrix_det_ne_zero`) plus Baker.
-- source:
--   Not found in the sources read; uses A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_two_by_two_config_entry_not_mem_span_logAlg {u : ℂ} (h : IsCandidate u)
    (m : ℕ) (w : Fin m → ℂ) (hgen : AlgebraicIndependent Qbar (Fin.cons u w : Fin (m + 1) → ℂ))
    (x y : Fin 2 → ℂ) (hx : LinearIndependent Qbar x) (hy : LinearIndependent Qbar y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, conj u} : Set ℂ) ∪ Set.range w)) :
    (∀ i, ∃ j, x i * y j ∉ Submodule.span Qbar LogAlg) ∧
      (∀ j, ∃ i, x i * y j ∉ Submodule.span Qbar LogAlg) := by
  sorry

end DiazModulus
