-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_lemma_6
-- name    : FlagshipMEA.Monopoly.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:43.155532+00:00
-- url     : https://prove2.me/theorems/e0acff88-8faf-4acb-9e19-2efe57894a51
-- title:
--   Lemma 6 — no tied MEA-index maximizers at positive optimal effort
-- statement:
--   Suppose products are pairwise distinct in their base utility and markup. If a feasible profit-maximizing allocation has positive total marketing effort $M$, exactly one product has maximal MEA index at $M$:
--
--   $$M>0\text{ and }m\text{ optimal}\quad\Longrightarrow\quad\left|\operatorname*{arg\,max}_iR_i(M)\right|=1.$$
--
--   This rules out a mixed optimal allocation supported by several tied index maximizers. **Formalization Note** Pairwise distinct products make explicit the genericity condition used at the end of the printed proof. The paper's proof has a gap in its inference from identical index curves to identical products for constant curves; this is recorded in the moderation notes.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 42 (PDF 44), Lemma 6; proof p. 43 (PDF 45)

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- Lemma 6 (p. 42), for pairwise distinct products: the index argmax at a
positive optimal total effort is unique. -/
theorem lemma_6 {n : ℕ} (D : Data n) (hS : D.Standing)
    (hfc : D.FcConcave) (hD : D.Distinct) (hn : 0 < n)
    (m : Fin n → ℝ) (hm : D.IsOptimal m) (hM : 0 < tme m) :
    ∃! i : Fin n, D.IsArgmaxR (tme m) i := by sorry

end FlagshipMEA.Monopoly
