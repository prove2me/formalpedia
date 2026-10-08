-- Prove2me | Theorems.Thm_AssocRealizations_SantosClass_proposition_5_5
-- name    : AssocRealizations.SantosClass.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:30.955684+00:00
-- url     : https://prove2.me/theorems/e4ee66e7-5334-4af2-a5cc-49907a245c6c
-- title:
--   Proposition 5.5 — the parallel pairs of a Santos associahedron
-- statement:
--   Let $T_0$ be a triangulation of an $(n+3)$-gon. There are exactly $n$ unordered pairs of distinct diagonals whose Santos normal vectors point in opposite directions. Moreover, for distinct diagonals $e,f$, their vectors are opposite exactly when one is a seed diagonal and the other is the diagonal inserted by flipping it:
--
--   $$
--   v_e(T_0)\text{ opposite }v_f(T_0)
--   \iff
--   \bigl(e\in T_0\ \text{and }(T_0\setminus\{e\})\cup\{f\}\text{ is a triangulation}\bigr)
--   \ \text{or the same with }e,f\text{ exchanged}.
--   $$
--
--   These pairs are the parallel facet pairs in the paper's full-dimensional associahedron. Their members together determine the set $B_{T_0}$ used in Lemma 5.6.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 23, Proposition 5.5

import Mathlib
import Definitions.Def_AssocRealizations_SantosClass_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

theorem proposition_5_5 (n : ℕ)
    (T₀ : Finset (Sym2 (Fin (n + 3))))
    (hT₀ : IsTriangulation (n + 3) T₀) :
    (Set.ncard {p : Sym2 (Sym2 (Fin (n + 3))) |
      ∃ e f : Sym2 (Fin (n + 3)),
        p = s(e, f) ∧ IsDiagonal e ∧ IsDiagonal f ∧ e ≠ f ∧
        Opposite (AssocRealizations.TypesMeet.santosVec T₀ e) (AssocRealizations.TypesMeet.santosVec T₀ f)}) = n ∧
    (∀ e f : Sym2 (Fin (n + 3)),
      IsDiagonal e → IsDiagonal f → e ≠ f →
      (Opposite (AssocRealizations.TypesMeet.santosVec T₀ e) (AssocRealizations.TypesMeet.santosVec T₀ f) ↔
        (e ∈ T₀ ∧ IsTriangulation (n + 3) (insert f (T₀.erase e))) ∨
        (f ∈ T₀ ∧ IsTriangulation (n + 3) (insert e (T₀.erase f))))) := by sorry

end AssocRealizations.SantosClass
