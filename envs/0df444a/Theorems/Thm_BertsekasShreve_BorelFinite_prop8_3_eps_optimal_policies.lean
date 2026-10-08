-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_prop8_3_eps_optimal_policies
-- name    : BertsekasShreve.BorelFinite.prop8_3_eps_optimal_policies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:51.66474+00:00
-- url     : https://prove2.me/theorems/f480bdf6-6e42-4dfc-83a9-1f3699757e02
-- title:
--   Proposition 8.3 — existence of ε-optimal nonrandomized (semi-)Markov policies under (F⁺) and (F⁻)
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1.
--   1. Under (F⁺), for each $\varepsilon>0$ there exists a nonrandomized Markov $\varepsilon$-optimal policy.
--   2. Under (F⁻), for each $\varepsilon>0$ there exist a nonrandomized semi-Markov $\varepsilon$-optimal policy and a (randomized) Markov $\varepsilon$-optimal policy.
--
--   Here $\pi$ is $\varepsilon$-optimal if, for every $x\in S$,
--   $$J_{N,\pi}(x)\le\begin{cases}J^*_N(x)+\varepsilon&\text{if }J^*_N(x)>-\infty,\\-1/\varepsilon&\text{if }J^*_N(x)=-\infty.\end{cases}$$
--
--   Under (F⁻) an $\varepsilon$-optimal nonrandomized policy may need to remember the initial state, which is why the semi-Markov class appears.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 200, Proposition 8.3

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy

namespace BertsekasShreve.BorelFinite

/-- **Proposition 8.3** (p. 200).
(F⁺) For each `ε > 0` there exists a nonrandomized Markov `ε`-optimal policy.
(F⁻) For each `ε > 0` there exist a nonrandomized semi-Markov `ε`-optimal policy and a
(randomized) Markov `ε`-optimal policy. -/
theorem prop8_3_eps_optimal_policies {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W) :
    (FPlus M → ∀ ε : ℝ, 0 < ε →
        ∃ π : Policy M, π.IsNonrandomized ∧ π.IsMarkov ∧ IsEpsOptimal M ε π) ∧
    (FMinus M → ∀ ε : ℝ, 0 < ε →
        (∃ π : Policy M, π.IsNonrandomized ∧ π.IsSemiMarkov ∧ IsEpsOptimal M ε π) ∧
        (∃ π : Policy M, π.IsMarkov ∧ IsEpsOptimal M ε π)) := by sorry

end BertsekasShreve.BorelFinite
