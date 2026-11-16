-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_lemma_5_2
-- name    : BulowKlemperer429.Bundling.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:25.688888+00:00
-- url     : https://prove2.me/theorems/5fb9ecb6-ba01-41e6-8e44-54e6d1e5ef4a
-- title:
--   Lemma 5.2 — the two-item seed: $4/5$, $21/25$ and $\mathrm{REV}(2+S_{\mathrm{seed}})=2$
-- statement:
--   Let $X,Y$ be independent, each taking values $0,1,2,3$ with probabilities $3/5,1/5,1/15,2/15$, and let $S_{\mathrm{seed}}=X+Y$. Then the separate revenue is
--   $$\mathrm{SREV}_{\mathrm{seed}}=\tfrac45,$$
--   selling the two items together at price $3$ earns $\mathrm{REV}_{\mathrm{seed}}=3\Pr[S_{\mathrm{seed}}\ge3]=\tfrac{21}{25}$, and the posted-price revenue of the shifted total is
--   $$\mathrm{REV}(2+S_{\mathrm{seed}})=\sup_{t\ge0}t\Pr[2+S_{\mathrm{seed}}\ge t]=2 .$$
--
--   These three numbers are the input of the completion construction that yields Theorem 5.3: the gain $21/25-4/5=1/25$, divided by $c=2$, is the improvement $0.02$ beyond two.
--
--   **Formalization Note** All three quantities are extended nonnegative reals; a sale at price $t$ means value at least $t$.
--
--   Differences from the source:
--   - encoding: selling the two items together at price 3 earns REV_seed; REV(2 + S_seed) → 3 · Pr[X + Y ≥ 3] and the posted-price revenue of the law of 2 + (X + Y), in [0,∞]; reason: a sale at price t means value at least t, the paper's posted-price convention (p. 6); the seed law is built as a sum of point masses
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 17, Lemma 5.2 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Seeds
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem lemma_5_2 :
    SREV (fun _ : Fin 2 => seedItemLaw) = 4 / 5 ∧
      3 * bundleLaw (fun _ : Fin 2 => seedItemLaw) {x | 3 ≤ x} = 21 / 25 ∧
      postedRevenue ((bundleLaw (fun _ : Fin 2 => seedItemLaw)).map (fun s => 2 + s)) = 2 := by sorry


end BulowKlemperer429.Bundling.Supplement
