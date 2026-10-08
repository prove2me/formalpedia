-- Prove2me | Theorems.Thm_CompOT_Metric_prop_2_2_gluing
-- name    : CompOT.Metric.prop_2_2_gluing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:21.090814+00:00
-- url     : https://prove2.me/theorems/376880ac-f98a-4019-9d9d-c1efcb716619
-- title:
--   Proof of Proposition 2.2, p. 378 — the glued matrix S = P diag(1/b̃) Q lies in U(a, c)
-- statement:
--   Let $a,b,c\in\Sigma_n$, $P\in U(a,b)$ and $Q\in U(b,c)$. Let $\tilde b_j=b_j$ if $b_j>0$ and $\tilde b_j=1$ otherwise. Then
--   $$S=P\,\mathrm{diag}(1/\tilde b)\,Q\in U(a,c).$$
--
--   This is the discrete gluing lemma: $S$ is nonnegative, its row sums are $a$ and its column sums are $c$. It is the coupling used to compare $\mathrm W_p(a,c)$ with $\mathrm W_p(a,b)+\mathrm W_p(b,c)$.
--
--   **Formalization Note** The page takes $P$ and $Q$ optimal; the membership claim does not use optimality, so it is stated for every $P\in U(a,b)$ and $Q\in U(b,c)$, which contains the page's case.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.2, p. 378

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- Proof of Proposition 2.2, p. 378: for `a, b, c ∈ Σ_n`, `P ∈ U(a, b)` and
`Q ∈ U(b, c)`, the glued matrix `S = P diag(1/b̃) Q` is nonnegative and lies in `U(a, c)`.
(The page takes `P`, `Q` optimal; optimality is not used for this claim.) -/
theorem prop_2_2_gluing {n : ℕ} (a b c : Fin n → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hc : c ∈ stdSimplex ℝ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b) (hQ : Q ∈ CompOT.Assignment.couplings b c) :
    glue b P Q ∈ CompOT.Assignment.couplings a c := by sorry

end CompOT.Metric
