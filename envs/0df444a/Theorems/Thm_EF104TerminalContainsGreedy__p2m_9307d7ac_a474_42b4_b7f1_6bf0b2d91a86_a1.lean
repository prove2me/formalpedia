-- Prove2me | Theorems.Thm_EF104TerminalContainsGreedy__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- name    : EF104TerminalContainsGreedy__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-19T09:35:39.593497+00:00
-- url     : https://prove2.me/theorems/a1a978aa-d041-4b6b-9848-fe8a8c0ddba8
-- title:
--   Earlier strict envy forces a terminal suffix allocation to contain its greedy profile
-- statement:
--   A suffix allocation whose every non-whole bundle has an earlier strict envier contains the greedy profile for the same guess. Prove containment by induction over the zipped orders, using suffix comparability, integral monotonicity, and the greedy earlier-agent inequalities. Strict envy preserves the argument when valuations have zero-value plateaus. No approximate envy-freeness hypothesis is required.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.10, Lemma 6 (restated p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

theorem EF104TerminalContainsGreedy__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (g : List ι × List ι) (hg : g ∈ guesses N)
    (A X : ι → Set ℝ)
    (hA : EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
      V P g.1 g.2 A)
    (hX : ∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2))
    (hstop :
    ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
      g.1.zip g.2 = before ++ p :: after →
        X p.1 = (P p.2).toSet ∨
        ∃ q ∈ before, (V q.1).value (X q.1) < (V q.1).value (X p.1)) :
    ∀ i ∈ N, A i ⊆ X i := by sorry
