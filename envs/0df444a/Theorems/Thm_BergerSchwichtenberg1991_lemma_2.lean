-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_lemma_2
-- name    : BergerSchwichtenberg1991.lemma_2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:55:31.639001+00:00
-- url     : https://prove2.me/theorems/2c7ff2fa-f3b1-4736-8533-346eb80d1f0c
-- title:
--   Lemma 2: Injectivity and Soundness of `EMB` and `EXTRACT`
-- statement:
--   Proves that `r =_α s ↔ EMB r = EMB s` and `EXTRACT(EMB r) =_α r` (Lemma 2, p. 205).
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Lemma 2, p. 205.

import Definitions.Def_BergerSchwichtenberg1991_Syntax

namespace BergerSchwichtenberg1991

theorem lemma_2 :
    (∀ r s : Term, AlphaEq r s ↔ EMB r = EMB s) ∧
    (∀ r : Term, AlphaEq (EXTRACT (EMB r)) r) ∧
    (∀ (r : Term) (k : Index), EMB (EMB r k) k = EMB r k) := by sorry

end BergerSchwichtenberg1991
