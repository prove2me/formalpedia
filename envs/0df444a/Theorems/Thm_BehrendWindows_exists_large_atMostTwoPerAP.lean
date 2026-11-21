-- Prove2me | Theorems.Thm_BehrendWindows_exists_large_atMostTwoPerAP
-- name    : BehrendWindows.exists_large_atMostTwoPerAP
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:49:09.927587+00:00
-- url     : https://prove2.me/theorems/46be8fad-ff27-4d07-a5a4-5b6eab839e98
-- title:
--   Large $m$-sparse sets with a bound uniform in $m$
-- statement:
--   There is a constant $C>0$ such that for all natural numbers $N$ and $m$ there is a set $T\subseteq\{0,1,\dots,N-1\}$ of integers which is $m$-sparse (no $m$-term arithmetic progression with non-zero common difference contains three elements of $T$) and satisfies
--
--   $$|T|\ \ge\ N\exp\!\Big(-C\sqrt{\log N\,\log m}\Big).$$
--
--   For $m=3$ this is Behrend's theorem on sets without three-term progressions. The constant is quantified before $N$ and $m$: one constant must serve every range and every progression length. The value of $C$ is left open, so the statement survives any improvement of the constant.
--
--   **Formalization Note** Lean's convention $\log 0=0$ makes $N=0$ and $m=0$ harmless, and for $m\le 2$ the sparseness condition is vacuous, so the statement carries no hypotheses on $N$ or $m$.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, Formalization targets, Goal; m = 3 case: F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, PNAS 32 (1946) 331-332, https://doi.org/10.1073/pnas.32.12.331

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP

namespace BehrendWindows

theorem exists_large_atMostTwoPerAP :
    ∃ C : ℝ, 0 < C ∧ ∀ N m : ℕ, ∃ T : Finset ℤ,
      T ⊆ Finset.Ico (0 : ℤ) N ∧ AtMostTwoPerAP T m ∧
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log N * Real.log m)) ≤ (T.card : ℝ) := by sorry

end BehrendWindows
