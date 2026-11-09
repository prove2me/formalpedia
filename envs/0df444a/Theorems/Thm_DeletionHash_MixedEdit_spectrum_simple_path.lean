-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_spectrum_simple_path
-- name    : DeletionHash.MixedEdit.spectrum_simple_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:34.822225+00:00
-- url     : https://prove2.me/theorems/a5291981-7539-422d-a367-d681f913306b
-- title:
--   Lemma 2.2 — spectrum simple path
-- statement:
--   Let $\Sigma$ be a finite alphabet of size $q\ge2$, let $k=2\lceil\log_q n\rceil+2$ and $L>k$, and put $m=L-1$. If a length-$n$ word $y$ is $m$-unique and $n\ge L$, then
--   $$\forall g:\ R_L(y)_g\in\{0,1\},\qquad R_L(y)\text{ carries the simple directed path of }y.$$
--   The path vertices are its successive length-$m$ windows and are pairwise distinct. Moreover every length-$n$ word $z$ satisfying $R_L(z)=R_L(y)$ equals $y$. This retains the Boolean, path and reconstruction clauses, supplying the word representation used in subsequent spectrum arguments.
--
--   Differences from the source:
--   - encoding: the actual simple directed path and Boolean spectrum → SpellsSimplePath with actual successive windows, plus the coordinate Boolean clause; reason: prefix/suffix incidence and the complete ordered vertex list encode the displayed path
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 2.2, printed p. 5 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Paths

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 2.2, printed p. 5 (PDF 7); generic L>k precedes equation (3). -/
theorem spectrum_simple_path {α : Type u} [Fintype α] [DecidableEq α]
    (n L : ℕ) (hq : 2 ≤ Fintype.card α) (hL : uniqueLength (Fintype.card α) n < L)
    (hn : L ≤ n) (y : Word α n) (hy : IsUnique (L-1) (letters y)) :
    (∀ g, spectrum L (letters y) g = 0 ∨ spectrum L (letters y) g = 1) ∧
    SpellsSimplePath L (letters y) ∧
    ∀ z : Word α n, spectrum L (letters z) = spectrum L (letters y) → z = y := by sorry

end DeletionHash.MixedEdit
