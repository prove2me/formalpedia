-- Prove2me | Theorems.Thm_CompOT_EntropicDual_proposition_4_3
-- name    : CompOT.EntropicDual.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:04.942914+00:00
-- url     : https://prove2.me/theorems/1d2287c4-7c99-495f-a297-5af6b6b77a9b
-- title:
--   Proposition 4.3 — unique entropic optimum and its Gibbs scaling
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be probability histograms, let $C\in\mathbb R^{n\times m}$, and let $\varepsilon>0$. The regularized transport problem has a unique optimal coupling $P$. There are nonnegative vectors $u$ and $v$ such that
--
--   $$
--   P_{ij}=u_i e^{-C_{ij}/\varepsilon}v_j\quad\text{for every }i,j.
--   $$
--
--   This factorization turns the regularized transport problem into a matrix scaling problem and supplies the primal optimizer used in the duality statement.
--
--   **Formalization Note** Zero entries are permitted in either histogram; the scaling vectors are nonnegative, as on the page. `Fin n` and `Fin m` index the book's one-based ranges.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 4.3 and (4.12), p. 432. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

namespace CompOT.EntropicDual

/-- Proposition 4.3, p. 432: the regularized problem has one minimizer, and it
factors as `Pᵢⱼ = uᵢ Kᵢⱼ vⱼ`. -/
theorem proposition_4_3 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      CompOT.EntropicLimit.IsEntropicOptimal C a b ε P ∧
      (∀ Q, CompOT.EntropicLimit.IsEntropicOptimal C a b ε Q → Q = P) ∧
      ∃ u : Fin n → ℝ, ∃ v : Fin m → ℝ,
        (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
        ∀ i j, P i j = u i * gibbs C ε i j * v j := by sorry

end CompOT.EntropicDual
