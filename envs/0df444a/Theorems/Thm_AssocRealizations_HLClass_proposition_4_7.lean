-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_proposition_4_7
-- name    : AssocRealizations.HLClass.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:57.241251+00:00
-- url     : https://prove2.me/theorems/71e911ee-f9a2-4e16-b013-8a6df3b776b7
-- title:
--   Proposition 4.7 — the n pairs of parallel facets of the Hohlweg–Lange associahedron
-- statement:
--   Let $\sigma \in \{+,-\}^{n-1}$ and write $\mathrm{sign}(r)$ for the sign of label $r$ in $\widetilde\sigma = \{+,-,\sigma,-,+\}$. For $j = 1, \dots, n$ put
--   $$i_j = \max\{0 \le r < j : \mathrm{sign}(r)\cdot\mathrm{sign}(j) = -\},\qquad k_j = \min\{j+1 < r \le n+2 : \mathrm{sign}(r)\cdot\mathrm{sign}(j+1) = -\}.$$
--   Then:
--
--   1. Two diagonals $\delta, \delta'$ of $P_{n+3}(\sigma)$ have opposite normal vectors (correspond to parallel facets of $\mathrm{Ass}^I_n(\sigma)$) if and only if, for some $j \in \{1, \dots, n\}$, they are the two diagonals of the quadrilateral with vertices $\{i_j, j, j+1, k_j\}$, i.e. their four endpoints are these labels and they cross.
--   2. For such a pair, the sets $S_\delta(\sigma)$ and $S_{\delta'}(\sigma)$ are $[j] = \{1, \dots, j\}$ and $\overline{[j]} = \{j+1, \dots, n+1\}$, so the normal vectors are $e_{[j]}$ and $e_{\overline{[j]}}$.
--   3. $\mathrm{Ass}^I_n(\sigma)$ has exactly $n$ pairs of parallel facets.
--
--   This is the explicit description of the parallel facets that the classification uses: a normal isomorphism must map these $n$ pairs to the $n$ pairs of the other associahedron.
--
--   **Formalization Note** "The diagonals of the quadrilateral" is read as its pair of crossing diagonals. The count is of unordered pairs of diagonals with opposite normals.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 17, Proposition 4.7

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Proposition 4.7 (p. 17): the parallel facets of `Ass^I_n(σ)`.
1. Two diagonals of `P_{n+3}(σ)` have opposite normals iff, for some `1 ≤ j ≤ n`, they are the
   two (crossing) diagonals of the quadrilateral with labels `{i, j, j + 1, k}`, where
   `i = max {0 ≤ r < j : sign r ≠ sign j}` and `k = min {j + 1 < r ≤ n + 2 : sign r ≠ sign (j + 1)}`.
2. The S-sets of such a pair are `[j] = {1, …, j}` and `{j + 1, …, n + 1}` (normals `e_{[j]}`
   and `e_{\overline{[j]}}`).
3. There are exactly `n` unordered parallel pairs. -/
theorem proposition_4_7 (n : ℕ) (σ : Fin (n - 1) → Bool) :
    (∀ e f : Sym2 (Fin (n + 3)), IsDiagonal e → IsDiagonal f →
      (AssocRealizations.TypesMeet.Opposite (hlVec n σ e) (hlVec n σ f) ↔
        ∃ j i k : ℕ, 1 ≤ j ∧ j ≤ n ∧
          IsGreatest {r : ℕ | r < j ∧ hlSign n σ r ≠ hlSign n σ j} i ∧
          IsLeast {r : ℕ | j + 1 < r ∧ r ≤ n + 2 ∧ hlSign n σ r ≠ hlSign n σ (j + 1)} k ∧
          (∃ a b c d : Fin (n + 3), e = s(a, b) ∧ f = s(c, d) ∧
            ({(hlLabel n σ a).val, (hlLabel n σ b).val, (hlLabel n σ c).val,
              (hlLabel n σ d).val} : Finset ℕ) = {i, j, j + 1, k}) ∧
          Crosses e f)) ∧
    (∀ e f : Sym2 (Fin (n + 3)), IsDiagonal e → IsDiagonal f →
      AssocRealizations.TypesMeet.Opposite (hlVec n σ e) (hlVec n σ f) →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          (((hlS n σ e).map Fin.valEmbedding = Finset.Icc 1 j ∧
              (hlS n σ f).map Fin.valEmbedding = Finset.Icc (j + 1) (n + 1)) ∨
            ((hlS n σ e).map Fin.valEmbedding = Finset.Icc (j + 1) (n + 1) ∧
              (hlS n σ f).map Fin.valEmbedding = Finset.Icc 1 j))) ∧
    {z : Sym2 (Sym2 (Fin (n + 3))) | ∃ e f, z = s(e, f) ∧ IsDiagonal e ∧ IsDiagonal f ∧
        AssocRealizations.TypesMeet.Opposite (hlVec n σ e) (hlVec n σ f)}.ncard = n := by sorry

end AssocRealizations.HLClass
