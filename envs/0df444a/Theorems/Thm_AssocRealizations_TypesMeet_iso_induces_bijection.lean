-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_iso_induces_bijection
-- name    : AssocRealizations.TypesMeet.iso_induces_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:55.961878+00:00
-- url     : https://prove2.me/theorems/78e7c82b-2c3e-44fb-88b5-19696ad2eb8f
-- title:
--   Theorem 6.1 proof — fan isomorphism preserves crossings and parallel facets
-- statement:
--   Let $T$ triangulate the $(n+3)$-gon, let $\sigma$ be a Hohlweg–Lange sign sequence, and suppose their type I and type II fans are normally isomorphic. There is then a bijection $\pi$ of polygon diagonals that preserves crossing and maps pairs of opposite facet normals to pairs of opposite facet normals:
--
--   $$e\mathrel{\pitchfork}f\iff\pi(e)\mathrel{\pitchfork}\pi(f),\qquad
--   v^{I}_{e}\parallel_{-}v^{I}_{f}\iff v^{II}_{\pi(e)}\parallel_{-}v^{II}_{\pi(f)}.$$
--
--   Here $\parallel_{-}$ means positive proportionality with opposite direction. This transfers the parallel-pair data used in the classification. **Formalization Note** The Lean bijection extends to all unordered vertex pairs and explicitly preserves the diagonal predicate both ways.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 28, proof of Theorem 6.1, opening paragraph

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem iso_induces_bijection (n : ℕ)
    (σ : Fin (n - 1) → Bool) (T : Finset (Sym2 (Fin (n + 3))))
    (hT : IsTriangulation (n + 3) T)
    (hiso : NormallyIsomorphic (hlFan σ) (santosFan T)) :
    ∃ π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)),
      (∀ e, IsDiagonal e ↔ IsDiagonal (π e)) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f →
        (Crosses e f ↔ Crosses (π e) (π f))) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f → e ≠ f →
        (Opposite (hlVec σ e) (hlVec σ f) ↔
          Opposite (santosVec T (π e)) (santosVec T (π f)))) := by sorry
end AssocRealizations.TypesMeet
