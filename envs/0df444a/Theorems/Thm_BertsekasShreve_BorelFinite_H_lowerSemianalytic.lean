-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_H_lowerSemianalytic
-- name    : BertsekasShreve.BorelFinite.H_lowerSemianalytic
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T06:04:40.869135+00:00
-- url     : https://prove2.me/theorems/739e4fcd-a8bd-4647-a43e-fb271121ccaf
-- title:
--   $H(x,u,J)=g(x,u)+\alpha\int J\,dt$ is lower semianalytic on $\Gamma$ when $J$ is
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1. Its ingredients are Borel spaces $S$, $C$, $W$; the analytic set $\Gamma=\{(x,u)\mid u\in U(x)\}$; a Borel disturbance kernel $p(dw\mid x,u)$; a Borel system function $f$; a discount factor $\alpha>0$; and a one-stage cost $g$ that is lower semianalytic on $\Gamma$. The state transition kernel is $t(B\mid x,u)=p(\{w\mid f(x,u,w)\in B\}\mid x,u)$.
--
--   For $J:S\to R^*$ define, as on p. 195,
--   $$H(x,u,J)=g(x,u)+\alpha\int_S J(x')\,t(dx'\mid x,u).$$
--   The integral is taken in the extended sense (43) of Chapter 7: $\int J=\int J^+-\int J^-$ with $\infty-\infty=\infty$. The sum uses the convention (42), $\infty-\infty=\infty$.
--
--   **Claim.** If $J:S\to R^*$ is lower semianalytic, then $(x,u)\mapsto H(x,u,J)$ is lower semianalytic on $\Gamma$: for every real $c$, the set $\{(x,u)\in\Gamma\mid H(x,u,J)<c\}$ is analytic.
--
--   This is the first half of the book's remark on p. 196, "By Lemma 7.30(4) and Propositions 7.47 and 7.48, $T(J)$ is lower semianalytic whenever $J$ is." Proposition 7.48 makes $(x,u)\mapsto\int J\,dt(\cdot\mid x,u)$ lower semianalytic. Lemma 7.30(4) then adds the lower semianalytic $g$. Proposition 7.47 (the partial infimum over $\Gamma$) gives the statement for $T(J)=\inf_{u\in U(x)}H(x,u,J)$. The same fact is what lets Lemma 8.2 apply the selection theorem, Proposition 7.50, to $H(\cdot,\cdot,J)$.
--
--   **Formalization note.** Lower semianalyticity on $\Gamma$ is `IsLowerSemianalyticOn M.Γ (H M J)`, i.e. $\Gamma$ is analytic and $\{z\in\Gamma\mid H(z)<c\}$ is analytic for every real $c$. The hypothesis on $J$ is `IsLowerSemianalyticOn Set.univ J`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 196 (paragraph before Lemma 8.2: "By Lemma 7.30(4) and Propositions 7.47 and 7.48, T(J) is lower semianalytic whenever J is"), the part given by Lemma 7.30(4) and Proposition 7.48 (p. 183), for the mapping H of p. 195

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

/-- **p. 196** (with Lemma 7.30(4) and Proposition 7.48). If `J : S → R*` is lower
semianalytic, then `H(x,u,J) = g(x,u) + α ∫ J(x′) t(dx′|x,u)` is lower semianalytic on
`Γ = {(x,u) | u ∈ U(x)}`; the integral is in the extended sense (43) of Chapter 7 and the sum
uses the convention (42). -/
theorem H_lowerSemianalytic {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (J : S → EReal) (hJ : IsLowerSemianalyticOn Set.univ J) :
    IsLowerSemianalyticOn M.Γ (H M J) := by sorry

end BertsekasShreve.BorelFinite
