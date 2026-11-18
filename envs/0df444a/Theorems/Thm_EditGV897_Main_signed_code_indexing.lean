-- Prove2me | Theorems.Thm_EditGV897_Main_signed_code_indexing
-- name    : EditGV897.Main.signed_code_indexing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:47:11.816089+00:00
-- url     : https://prove2.me/theorems/e8efd63d-7b99-4c04-b657-d2fb740b903b
-- title:
--   Signed-bound indexing and exact message recovery
-- statement:
--   Let $F$ be a family of affine edit maps covering all distinct confusable pairs of binary length-$n$ words, and let $P=(H,\beta)$ be shared parameters, with one syndrome bit per row. Assume the affine-system counting routine and collision-witness counting routine agree with their finite-set specifications. Set $K=n-|H|-1$ and suppose the chosen coset satisfies
--
--   $$2^K\le |D_{H,\beta}|-W_H(D_{H,\beta}).$$
--
--   The signed-bound encoder then injects all $K$-bit messages into separated words in that coset. For every message $u$, its output list has length $n$, equals the ordered list of its output word $x$, and satisfies
--
--   $$Hx=\beta,\qquad x\text{ is separated},\qquad \operatorname{Inv}(x)=u.$$
--
--   The residual message index after the final encoding step is zero. This is the semantic part of the signed enumerative construction in Lemma 3; the exact counting assumptions are interfaces supplied by Lemma 1. Polynomial-time program realizations are separate from this statement.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §4.3, equation (12) and proof of Lemma 3, printed pp.12–13 / PDF pp.13–14

import Definitions.Def_EditGV897_Main_Codec
open EditGV897.Main

theorem EditGV897.Main.signed_code_indexing {n t : ℕ} (F : Family n) (P : Parameters n)
    (hF : EditFamily t F) (hβ : P.beta.length = P.rows.length)
    (ha : ∀ E : List (Equation n), affineCount E = (affineSet E).card)
    (hw : ∀ E : List (Equation n), witnessCount F P.rows E = witnessSum F P.rows (affineSet E))
    (hroot : (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta)) :
    Function.Injective (encodeWord F P) ∧
    ∀ u : Word (messageLength P),
      encodeList F P u = wordList (encodeWord F P u) ∧ (encodeList F P u).length = n ∧
      syndrome P.rows (encodeWord F P u) = P.beta ∧ Separated t P.rows (encodeWord F P u) ∧
      (encodeSteps F P n [] (messageIndex (wordList u))).2 = 0 ∧
      inverseList F P (wordList (encodeWord F P u)) = wordList u := by sorry
