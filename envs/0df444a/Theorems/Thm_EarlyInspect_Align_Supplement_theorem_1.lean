-- Prove2me | Theorems.Thm_EarlyInspect_Align_Supplement_theorem_1
-- name    : EarlyInspect.Align.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T03:39:47.440188+00:00
-- url     : https://prove2.me/theorems/0aaf8f4f-7f52-4f2a-a928-7b30add09c61
-- title:
--   Theorem 1, p. 60 — under scheme $[M]$ the agent orders up to $r^{-1}(M/\hat c_o)$ if this is at least $I$, and to $I$ otherwise, where $r=F/f$
-- statement:
--   Let the period demand $D$ have a probability law $P$ on $\mathbb R$ with density $f$, distribution function $F$ and $\mathbb E[D^-]<\infty$. The support is an open interval $J$, bounded or unbounded: $f$ is continuous and positive on $J$ and zero outside it. On $J$ let $r(x)=F(x)/f(x)$ be the reciprocal of the reversed hazard rate. Assume that $r$ is injective on $J$ and, in the single case where $J$ is bounded above but not below, that $r$ is strictly increasing on $J$.
--
--   The agent starts with inventory $I$ and, under scheme $[M]$ with $\hat c_o>0$, minimizes over order-up-to levels $S\ge I$ the score
--
--   $$
--   \mathrm{ETPM}_{[M]}(S)=\hat c_o\,\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{D\ge S\}.
--   $$
--
--   If $s_0\in J$ satisfies $r(s_0)=M/\hat c_o$, that is $s_0=r^{-1}(M/\hat c_o)$, then the agent's problem has exactly one solution:
--
--   $$
--   \operatorname*{argmin}_{S\ge I}\mathrm{ETPM}_{[M]}(S)=\{\max(I,s_0)\}.
--   $$
--
--   So the agent orders up to $r^{-1}(M/\hat c_o)$ when this is at least $I$, and does not order otherwise. The result gives the principal the agent's response to every penalty under end-of-period inspection. The normal laws of the paper's model ($J=\mathbb R$) and the uniform laws it names ($J$ a bounded interval) are both covered.
--
--   **Formalization Note** $P$ is given with $P=f\,dx$, $J$ is an open order-connected set of reals, $\hat c_o$ is `chat`, and the agent's choice is the set of minimizers `argminFrom`. The extra monotonicity hypothesis binds only when $J=(-\infty,b)$. For every other interval it is absent, since `BddAbove J → ¬ BddBelow J` cannot then be met.
--
--   Differences from the source:
--   - reading: a demand distribution with pdf f and cdf F, and r(x) = F(x)/f(x) → a probability law with a density that is continuous and positive on an open interval J and zero outside, with r considered on J; reason: the explicit regularity reading of the brief makes F/f and its inverse usable pointwise; the interval version also covers the uniform law named on p. 60, while J = ℝ recovers the whole full-support class required by the brief
--   - reading: S = r⁻¹(M/ĉ_o), after the remark that the reversed hazard rate f/F is decreasing for log-concave densities → r is injective on J and some s₀ in J has r(s₀) = M/ĉ_o; reason: injectivity and membership of M/ĉ_o in the range make the inverse notation meaningful; they alone do not imply that r increases on an upper-bounded support
--   - generalization: the normal demand model of §3 and the brief’s full-support density reading of Theorem 1 → also allows interval supports, imposing StrictMonoOn r J only when J is bounded above and not below; reason: J = ℝ makes the conditional hypothesis vacuous, so no full-support instance is excluded; bounded-below supports include the uniform examples; the extra condition controls only upper-bounded, lower-unbounded supports in this extension and is not claimed to follow from inverse notation or to have been printed in the theorem
--   - encoding: the expectation in (3), and a scheme parameter ĉ_o that is divided by → E[D⁻] finite and ĉ_o > 0; reason: the score (3) is otherwise infinite or is not an overage penalty, and Lean would return a default value for the integral
--   - encoding: the optimal level is r⁻¹(M/ĉ_o) if at least I, and I otherwise → the set of minimizers over S ≥ I equals {max(I, s₀)}; reason: the two cases are one maximum, and the singleton expresses "the optimal level"
--   - generalization: I is the starting inventory level, nonnegative in the paper → I is any real number; reason: the formula needs no sign of I and specializes to every I ≥ 0
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 60 (PDF 7), §4.1.1, Theorem 1

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model
import Definitions.Def_EarlyInspect_Align_Supplement_SchemeM

namespace EarlyInspect.Align.Supplement

open MeasureTheory

theorem theorem_1 (P : Measure ℝ) [IsProbabilityMeasure P] (f : ℝ → ℝ) (J : Set ℝ)
    (hJopen : IsOpen J) (hJconn : J.OrdConnected)
    (hfcont : ContinuousOn f J) (hfpos : ∀ x ∈ J, 0 < f x) (hfzero : ∀ x ∉ J, f x = 0)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hneg : Integrable (fun x => max (-x) 0) P)
    (hinj : Set.InjOn (revHazardRecip P f) J)
    (hincr : BddAbove J → ¬ BddBelow J → StrictMonoOn (revHazardRecip P f) J)
    (chat M s₀ I : ℝ) (hchat : 0 < chat) (hs₀ : s₀ ∈ J)
    (hroot : revHazardRecip P f s₀ = M / chat) :
    EarlyInspect.Align.argminFrom (agentCostM P chat M) I = {max I s₀} := by sorry

end EarlyInspect.Align.Supplement
