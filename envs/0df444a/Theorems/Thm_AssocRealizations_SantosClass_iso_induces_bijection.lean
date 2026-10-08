-- Prove2me | Theorems.Thm_AssocRealizations_SantosClass_iso_induces_bijection
-- name    : AssocRealizations.SantosClass.iso_induces_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:37.212683+00:00
-- url     : https://prove2.me/theorems/f85f8a73-8f60-4f19-aacb-7a1aef7f3052
-- title:
--   Proof of Corollary 5.7 — fan isomorphism preserves crossings and parallel pairs
-- statement:
--   Let $T_1,T_2$ be triangulations of the same $(n+3)$-gon. If their Santos fans are normally isomorphic, the isomorphism induces a bijection $\pi$ of polygon diagonals. It preserves crossings and opposite normal directions:
--
--   $$
--   e\text{ crosses }f\iff\pi(e)\text{ crosses }\pi(f),\qquad
--   v_e(T_1)\text{ opposite }v_f(T_1)\iff
--   v_{\pi(e)}(T_2)\text{ opposite }v_{\pi(f)}(T_2).
--   $$
--
--   The second equivalence applies to distinct diagonals. This isolates the geometric step used before invoking the polygon symmetry theorem and the parallel-facet classification.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 24, proof of Corollary 5.7

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

theorem iso_induces_bijection (n : ℕ)
    (T₁ T₂ : Finset (Sym2 (Fin (n + 3))))
    (h₁ : IsTriangulation (n + 3) T₁)
    (h₂ : IsTriangulation (n + 3) T₂)
    (hiso : AssocRealizations.TypesMeet.NormallyIsomorphic (AssocRealizations.TypesMeet.santosFan T₁) (AssocRealizations.TypesMeet.santosFan T₂)) :
    ∃ π : Sym2 (Fin (n + 3)) ≃ Sym2 (Fin (n + 3)),
      (∀ e, IsDiagonal e ↔ IsDiagonal (π e)) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f →
        (Crosses e f ↔ Crosses (π e) (π f))) ∧
      (∀ e f, IsDiagonal e → IsDiagonal f → e ≠ f →
        (Opposite (AssocRealizations.TypesMeet.santosVec T₁ e) (AssocRealizations.TypesMeet.santosVec T₁ f) ↔
         Opposite (AssocRealizations.TypesMeet.santosVec T₂ (π e)) (AssocRealizations.TypesMeet.santosVec T₂ (π f)))) := by sorry

end AssocRealizations.SantosClass
