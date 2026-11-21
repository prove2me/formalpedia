-- Prove2me | Theorems.Thm_BehrendWindows_exists_atMostTwoPerAP_of_box
-- name    : BehrendWindows.exists_atMostTwoPerAP_of_box
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:47:59.399674+00:00
-- url     : https://prove2.me/theorems/feed4a85-9f05-4290-99d8-edc18ba3dbc7
-- title:
--   Finite Behrend bound for $m$-sparse sets
-- statement:
--   Let $S,d,m\in\mathbb{N}$ with $S\ge 1$, $d\ge 1$ and $m\ge 3$. There is an $m$-sparse set $T\subseteq\{0,1,\dots,(md)^S-1\}$ of integers with
--
--   $$|T|\ \ge\ \frac{d^{S}}{S\,d^{2}}.$$
--
--   This is the explicit finite form of the construction: the bound comes from the most populated sphere in the box $\{0,\dots,d-1\}^S$, and the free parameters $S$ and $d$ are later chosen as functions of $N$ and $m$ to obtain the goal theorem.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, Formalization targets, supporting target (finite form), milestone 4

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP

namespace BehrendWindows

theorem exists_atMostTwoPerAP_of_box (S d m : ℕ) (hS : 1 ≤ S) (hd : 1 ≤ d) (hm : 3 ≤ m) :
    ∃ T : Finset ℤ, T ⊆ Finset.Ico (0 : ℤ) ((m * d) ^ S : ℕ) ∧ AtMostTwoPerAP T m ∧
      (d : ℝ) ^ S / (S * (d : ℝ) ^ 2) ≤ (T.card : ℝ) := by sorry

end BehrendWindows
