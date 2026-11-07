-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_T_lowerSemianalytic
-- name    : BertsekasShreve.BorelFinite.T_lowerSemianalytic
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:53:23.723794+00:00
-- url     : https://prove2.me/theorems/ccce5390-9ab1-493a-aa04-2013ee67268c
-- title:
--   The DP operator $T$ maps lower semianalytic functions to lower semianalytic functions
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 (Borel spaces $S$, $C$, $W$, analytic constraint set $\Gamma=\{(x,u)\mid u\in U(x)\}$, Borel disturbance kernel $p(dw\mid x,u)$, Borel system function $f$, discount $\alpha>0$, one-stage cost $g$ lower semianalytic on $\Gamma$), with state transition kernel $t(B\mid x,u)=p(\{w\mid f(x,u,w)\in B\}\mid x,u)$. For $J:S\to R^*$ let
--   $$T(J)(x)=\inf_{u\in U(x)}\Big\{g(x,u)+\alpha\int_S J(x')\,t(dx'\mid x,u)\Big\},$$
--   where the integral is taken in the extended sense (43) of Chapter 7 ($\int J=\int J^+-\int J^-$, with $\infty-\infty=\infty$) and the sum uses the convention (42) ($\infty-\infty=\infty$).
--
--   **Claim (p. 196).** If $J:S\to R^*$ is lower semianalytic, then $T(J)$ is lower semianalytic.
--
--   The book justifies this in one sentence: "By Lemma 7.30(4) and Propositions 7.47 and 7.48, $T(J)$ is lower semianalytic whenever $J$ is." Proposition 7.48 makes $(x,u)\mapsto\int J\,dt(\cdot\mid x,u)$ lower semianalytic, Lemma 7.30(4) handles the sum with $g$, and Proposition 7.47 handles the partial infimum over the analytic set $\Gamma$.
--
--   **Formalization note.** "Lower semianalytic" is `IsLowerSemianalyticOn Set.univ`: $S$ is analytic and $\{x\mid J(x)<c\}$ is analytic for every real $c$. This fact is used, with $J=T^{k-1}(J_0)$, in the proof of Proposition 8.2 (to apply Lemma 8.2 / Proposition 7.50 to the iterates of the DP algorithm).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 196 (paragraph after Definition 8.5 and before Lemma 8.2): "By Lemma 7.30(4) and Propositions 7.47 and 7.48, T(J) is lower semianalytic whenever J is."

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

/-- **p. 196** (text preceding Lemma 8.2). "By Lemma 7.30(4) and Propositions 7.47 and 7.48,
`T(J)` is lower semianalytic whenever `J` is." Here `T(J)(x) = inf_{u ∈ U(x)} {g(x,u) +
α ∫ J(x′) t(dx′|x,u)}` (Definition 8.5), with the integral in the extended sense (43) of
Chapter 7 and the sum taken with the convention (42). -/
theorem T_lowerSemianalytic {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (J : S → EReal) (hJ : IsLowerSemianalyticOn Set.univ J) :
    IsLowerSemianalyticOn Set.univ (T M J) := by sorry

end BertsekasShreve.BorelFinite
