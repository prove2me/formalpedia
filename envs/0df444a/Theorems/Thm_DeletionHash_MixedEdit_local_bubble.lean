-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_local_bubble
-- name    : DeletionHash.MixedEdit.local_bubble
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:05.634073+00:00
-- url     : https://prove2.me/theorems/f9ff2cf0-9847-49d8-b36c-eef837fd5cbb
-- title:
--   Lemma 2.4 — local bubble
-- statement:
--   In the standing proof regime, let $x$ be a $k$-unique length-$n$ word and apply one valid edit replacing the actual substring $U$ by $V$, with at least $2(L+b)$ source letters on either side. There exist actual flanks $A,B$ and unchanged exterior words $X,Y$ such that $x=XAUBY$, the target is $XAVBY$, and the edit begins at $|X|+|A|$. For $P=AUB$ and $P'=AVB$,
--   $$R_L(\text{target})-R_L(x)=R_L(P')-R_L(P),\qquad m-k-b\le |A|,|B|\le m.$$
--   Here $m=L-1$, $U\ne V$ and $|U|,|V|\le b$. Both local words have length between $L$ and $2m+b$, share their first and last $m$ letters, and spell simple paths meeting only at those endpoints. These complete local geometry conclusions connect a genuine edit to Definition 2.5.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: local substrings with corresponding unchanged exterior → explicit exterior lists X,Y, actual edit location and a Bubble pair, together with explicit flank bounds and spectrum identity; reason: the decomposition states which occurrence is edited and exposes every geometric clause of equation (4)
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 2.4, printed p. 7 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 2.4: actual flanks and unchanged exterior, full path and length geometry. -/
theorem local_bubble {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (e : Edit α)
    (he : ValidEdit b (letters x) e) (hleft : 2*(L+b) ≤ e.position)
    (hright : e.position+e.removed+2*(L+b) ≤ n) :
    let U := window e.removed (letters x) e.position
    ∃ A B X Y : List α,
      letters x = X ++ A ++ U ++ B ++ Y ∧
      applyEdit e (letters x) = X ++ A ++ e.replacement ++ B ++ Y ∧
      e.position = X.length + A.length ∧
      (L-1)-k-b ≤ A.length ∧ A.length ≤ L-1 ∧
      (L-1)-k-b ≤ B.length ∧ B.length ≤ L-1 ∧
      Bubble k L b (A ++ U ++ B) (A ++ e.replacement ++ B) ∧
      spectrum L (applyEdit e (letters x)) - spectrum L (letters x) =
        spectrum L (A ++ e.replacement ++ B) - spectrum L (A ++ U ++ B) := by sorry

end DeletionHash.MixedEdit
