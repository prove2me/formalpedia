-- Prove2me | Theorems.Thm_BroughanRH_divisibilityCycles
-- name    : BroughanRH.divisibilityCycles
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:19:24.476914+00:00
-- url     : https://prove2.me/theorems/fa0f8ebe-ca09-4589-99a4-59982e0ff5b6
-- title:
--   Odd and even cycles in the divisibility graph
-- statement:
--   The difference between the counts of odd and even directed simple cycles of the loopless divisibility graph is $O_\varepsilon(N^{1/2+\varepsilon})$. Each cycle starts at $1$, traverses a nonempty increasing divisibility chain, then returns to $1$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.10. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem divisibilityCycles :
    let chains (N : ℕ) := (Finset.Icc 2 N).powerset.filter fun S =>
      S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a ∣ b
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ S ∈ chains N, (-1 : ℝ)^S.card)
      (fun N : ℕ => (N : ℝ)^(1/2 + ε)) := by sorry

end BroughanRH
