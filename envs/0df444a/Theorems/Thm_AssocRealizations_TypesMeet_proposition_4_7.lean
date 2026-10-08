-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_proposition_4_7
-- name    : AssocRealizations.TypesMeet.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:06.572443+00:00
-- url     : https://prove2.me/theorems/0282f5b9-48c1-46a8-a9e1-ff4c0202a9c4
-- title:
--   Proposition 4.7 — parallel pairs in the Hohlweg–Lange fan
-- statement:
--   For each $j=1,\ldots,n$, let $i_j$ be the greatest label below $j$ with sign opposite to $j$, and let $k_j$ be the least label above $j+1$ with sign opposite to $j+1$. The two diagonals of the quadrilateral with labels $\{i_j,j,j+1,k_j\}$ have opposite type I normal rays, and their sets $S_\delta(\sigma)$ are $[j]=\{1,\ldots,j\}$ and $\overline{[j]}=\{j+1,\ldots,n+1\}$, so the normals are $e_{[j]}$ and $e_{\overline{[j]}}$. Conversely, every pair of distinct diagonal facets with opposite type I normals is one of these pairs:
--
--   $$v^{I}_{e}\parallel_{-}v^{I}_{f}\iff
--   \exists j\in\{1,\ldots,n\}:\quad e,f\text{ cross, their endpoints are }\{i_j,j,j+1,k_j\},\ \{S_e,S_f\}=\{[j],\overline{[j]}\}.$$
--
--   This identifies the $n$ parallel-facet pairs of a type I associahedron. **Formalization Note** Vertices in the formula are labels; crossing is evaluated on cyclic positions. Both arguments are explicitly required to be diagonals, as facets are indexed only by diagonals.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 17, Proposition 4.7

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem proposition_4_7 (n : ℕ) (σ : Fin (n - 1) → Bool)
    (e f : Sym2 (Fin (n + 3))) (he : IsDiagonal e) (hf : IsDiagonal f)
    (hne : e ≠ f) :
    Opposite (hlVec σ e) (hlVec σ f) ↔
      ∃ j : Fin n, ∃ a b c d : Fin (n + 3),
        (hlLabel σ a).val = hlI σ (j.val + 1) ∧
        (hlLabel σ b).val = j.val + 1 ∧
        (hlLabel σ c).val = j.val + 2 ∧
        (hlLabel σ d).val = hlK σ (j.val + 1) ∧
        Crosses e f ∧
        (∀ p : Fin (n + 3), (p ∈ e ∨ p ∈ f) ↔
          (p = a ∨ p = b ∨ p = c ∨ p = d)) ∧
        ((hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1)) ∨
          (hlS σ f = Finset.univ.filter
              (fun k : Fin (n + 3) => 1 ≤ k.val ∧ k.val ≤ j.val + 1) ∧
            hlS σ e = Finset.univ.filter
              (fun k : Fin (n + 3) => j.val + 2 ≤ k.val ∧ k.val ≤ n + 1))) := by sorry
end AssocRealizations.TypesMeet
