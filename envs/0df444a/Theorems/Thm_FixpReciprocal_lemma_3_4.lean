-- Prove2me | Theorems.Thm_FixpReciprocal_lemma_3_4
-- name    : FixpReciprocal.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:53.072199+00:00
-- url     : https://prove2.me/theorems/0317e73e-df52-47d3-acde-6e91cf7780d8
-- title:
--   Lemma 3.4 — restricted generalized circuits are FIXP-complete (cited: [FGH+23, Proposition 5.6])
-- statement:
--   Let $\mathcal F$ consist of the gate functions
--   $$u\mapsto1-u,\qquad(u,v)\mapsto[\![u+v]\!],\qquad u\mapsto u^2.$$
--   Finding a solution to an $\mathcal F$-generalized circuit is FIXP-complete.
--
--   This is the source of the hardness of the goal theorem. The paper cites it from Filos-Ratsikas, Giannakopoulos, Hollender, Lazos and Poças and gives no proof of it, so a proof here must follow the cited route.
--
--   Differences from the source:
--
--   - reading: polynomial time → Mathlib's Turing.TM2ComputableInPolyTime over fixed binary encodings in the alphabet Sym; reason: the paper names no machine model; §3, p.10 measures input size by bit length
--   - encoding: 0-based indices, instances as subtypes, the list-of-triples recovery data → the corresponding Lean data; reason: same instances and reductions; see the definitions' notes
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Lemma 3.4, p.11 (PDF p.13), citing [FGH+23, Proposition 5.6]

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_FixpReciprocal_squareProblem

namespace FixpReciprocal

/-- **Lemma 3.4 (Restricted Generalized Circuits; [FGH+23, Proposition 5.6], cited).** Let `F` consist of the
gate functions `u ↦ 1 − u`, `(u, v) ↦ ⟦u + v⟧`, and `u ↦ u²`. Finding a solution to an `F`-generalized circuit
is FIXP-complete.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Lemma 3.4, p.11. The paper cites this result and gives no proof of it.

**Formalization Note.** Stated with this paper's Definitions 3.1–3.3, as the paper does. -/
theorem lemma_3_4 : FIXPComplete squareProblem := by sorry

end FixpReciprocal
