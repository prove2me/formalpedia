-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_lemma_2
-- name    : BergerSchwichtenberg1991V2.lemma_2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:14:06.829691+00:00
-- url     : https://prove2.me/theorems/a19a373c-2df0-437b-9e4f-d02dacd4585c
-- title:
--   Lemma 2 — Embedding, extraction, and idempotence
-- statement:
--   Two raw terms are $\alpha$-equivalent exactly when their indexed families agree. Extracting from any embedded term gives an $\alpha$-equivalent representative. Standardizing an already standardized term again at the same prefix returns the same syntax.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Lemma 2, p. 205. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Syntax

namespace BergerSchwichtenberg1991V2

/-- Lemma 2 (p. 205). The families distinguish α-classes, extraction recovers an
α-variant, and standardizing again at the same prefix gives the same term. These
statements apply also to raw terms without a typing derivation. -/
theorem lemma_2 :
    (∀ r s : Term, AlphaEq r s ↔ EMB r = EMB s) ∧
    (∀ r : Term, AlphaEq (EXTRACT (EMB r)) r) ∧
    (∀ (r : Term) (k : Index), EMB (EMB r k) k = EMB r k) := by sorry

end BergerSchwichtenberg1991V2
