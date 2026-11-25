-- Prove2me | Theorems.Thm_Arxiv2610_39302_merging_within_states_lowers_mixing
-- name    : Arxiv2610_39302.merging_within_states_lowers_mixing
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:05:56.967368+00:00
-- url     : https://prove2.me/theorems/90a45d1b-e82c-5ada-bc1a-97189004d24d
-- title:
--   Theorem 4, scope: merging observations of one state
-- statement:
--   Let a modality have finitely many observations $x$ with law $\omega>0$, each of a world state $s(x)$, every state having positive probability, and let $W$ be a symmetric law on pairs of observations with marginal $\omega$. Group the observations by a surjective map $c:X\to Y$ whose groups each lie within one state ($s=s'\circ c$), and give the merged observations the summed law $\omega'$ and positive-pair law $W'(y,y')=\sum_{c(x)=y,\,c(x')=y'}W(x,x')$. Then merging leaves the induced world kernel unchanged, $\pi_{W'}=\pi_W$, and can only lower $\eta$ and $\varepsilon$:
--
--   $$\eta'\le\eta,\qquad\varepsilon'\le\varepsilon.$$
--
--   **Formalization Note** The statement formalizes the quantitative part of the paragraph: $\pi_W$ unchanged, $\eta$ and $\varepsilon$ not increased. The identification of group-constant encoders with encoders of the merged observations, and the remark that other inductive biases are outside the model, are not part of the Lean statement.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c061 (b); Appendix A.4, formal Theorem 4, paragraph 'Special cases and scope', PDF p. 22

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem merging_within_states_lowers_mixing {Z X Y : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ω : X → ℝ) (s : X → Z) (W : X → X → ℝ) (hW : IsPairLaw ω W)
    (hp : ∀ z, 0 < stateMarg ω s z)
    (c : X → Y) (hc : Function.Surjective c) (s' : Y → Z) (hs' : ∀ x, s' (c x) = s x) :
    inducedKernel s' (mergeLaw c W) = inducedKernel s W ∧
    nuisanceTop (mergeWeights c ω) s' (mergeLaw c W) ≤ nuisanceTop ω s W ∧
    mixNorm (mergeWeights c ω) s' (mergeLaw c W) ≤ mixNorm ω s W := by sorry

end Arxiv2610_39302
