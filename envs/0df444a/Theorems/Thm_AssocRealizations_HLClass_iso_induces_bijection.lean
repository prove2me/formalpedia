-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_iso_induces_bijection
-- name    : AssocRealizations.HLClass.iso_induces_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:30.078861+00:00
-- url     : https://prove2.me/theorems/3275a2bb-31bd-493d-9df5-a5e87bb51062
-- title:
--   Proof of Theorem 4.9, p. 17 — a normal isomorphism induces a crossing-preserving bijection of diagonals that preserves parallel pairs
-- statement:
--   Let $\sigma_1, \sigma_2 \in \{+,-\}^{n-1}$ and suppose the normal fans of the Hohlweg–Lange associahedra $\mathrm{Ass}^I_n(\sigma_1)$ and $\mathrm{Ass}^I_n(\sigma_2)$ are linearly isomorphic. Then there is a bijection $\pi$ of the chords of the $(n+3)$-gon such that
--
--   1. $\pi$ maps diagonals to diagonals and non-diagonals to non-diagonals;
--   2. for all diagonals $\delta, \delta'$: $\delta$ crosses $\delta'$ iff $\pi(\delta)$ crosses $\pi(\delta')$;
--   3. for all diagonals $\delta, \delta'$: the normals $v_\delta(\sigma_1)$ and $v_{\delta'}(\sigma_1)$ are opposite iff $v_{\pi(\delta)}(\sigma_2)$ and $v_{\pi(\delta')}(\sigma_2)$ are opposite.
--
--   Here the diagonals are those of $P_{n+3}(\sigma_1)$ and $P_{n+3}(\sigma_2)$ respectively, both read on the positions of a common $(n+3)$-gon. This is the first step of the proof of Theorem 4.9: a linear isomorphism of the normal fans induces an automorphism of the face lattice of the associahedron and preserves the property of a pair of facets being parallel. Combined with Lemma 2.2 it yields a dihedral symmetry of the polygon that maps parallel pairs to parallel pairs.
--
--   **Formalization Note** The fans are the fans of the vectors $v_\delta(\sigma)$ (see the Setting item); facets are parallel when their normals are negative multiples of each other.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 17, proof of Theorem 4.9, first paragraph

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Proof of Theorem 4.9 (p. 17): a linear isomorphism between the normal fans of
`Ass^I_n(σ₁)` and `Ass^I_n(σ₂)` induces a bijection of the chords of the (n + 3)-gon that maps
diagonals onto diagonals, preserves crossing, and maps the parallel pairs of `Ass^I_n(σ₁)`
exactly onto the parallel pairs of `Ass^I_n(σ₂)`. -/
theorem iso_induces_bijection (n : ℕ) (σ₁ σ₂ : Fin (n - 1) → Bool)
    (h : AssocRealizations.TypesMeet.NormallyIsomorphic (hlFan n σ₁) (hlFan n σ₂)) :
    ∃ π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)),
      (∀ e, IsDiagonal e ↔ IsDiagonal (π e)) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f → (Crosses e f ↔ Crosses (π e) (π f))) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f →
        (AssocRealizations.TypesMeet.Opposite (hlVec n σ₁ e) (hlVec n σ₁ f) ↔
          AssocRealizations.TypesMeet.Opposite (hlVec n σ₂ (π e)) (hlVec n σ₂ (π f)))) := by sorry

end AssocRealizations.HLClass
