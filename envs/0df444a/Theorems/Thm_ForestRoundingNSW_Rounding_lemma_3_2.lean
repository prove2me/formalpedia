-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_lemma_3_2
-- name    : ForestRoundingNSW.Rounding.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:51:13.482234+00:00
-- url     : https://prove2.me/theorems/7c9baa58-7c26-42f9-b9e6-62088b7f2fd1
-- title:
--   Lemma 3.2 — balanced individual rounding preserves marginals and loses at most 2/(e ln 2) in geometric value
-- statement:
--   Let $f:2^G\to\mathbb R_{\ge0}$ be normalized, monotone and submodular with multilinear extension $F$, let $x\in[0,1]^G$, and let $b>0$ with $f(\{j\})\le b$ for every $j\in G$. Let $S$ be the output of Algorithm 1 on $x$ (with exact gradients of $F$), for any choice rule. Then, with $C=2/(e\ln2)$:
--
--   (3.2a) $\Pr[j\in S]=x_j$ for every $j\in G$;
--
--   (3.2b) $$\mathbb E\big[\ln\max\{f(S),b\}\big]\;\ge\;\ln\max\Big\{b,\frac{F(x)}{C}\Big\};$$
--
--   and the algorithm uses at most $|G|$ rounding steps.
--
--   This is the paper's individual rounding: it confines the whole loss in expected logarithmic value to one final Bernoulli choice, and its preserved marginals let Algorithm 2 couple the agents on a forest.
--
--   Differences from the source:
--   - encoding: f : 2^G → ℝ≥0 normalized monotone submodular → f : Finset X → ℝ with IsNMS f on a finite type X; reason: nonnegativity follows from normalized and monotone; Lean convention for the ground set
--   - reading: Choose two fractional coordinates r, s → the statement holds for every choice rule ρ, a function of the current state naming two distinct fractional coordinates whenever there are at least two; reason: the paper leaves the choice open, so the lemma is claimed for every choice
--   - encoding: the random output of Algorithm 1, Pr and E → the law alg1Law (a PMF built step by step), finite sums over it; reason: same distribution
--   - encoding: the algorithm uses at most |G| rounding steps → every outcome of the run with a budget of |G| rounding steps (loop iterations and the final choice) has finished; reason: a run needing more steps would be unfinished at the budget
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), pp. 19–20, Lemma 3.2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions
import Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding

open NonmonotoneSubmod.Shared

namespace ForestRoundingNSW.Rounding

theorem lemma_3_2 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (hf : IsNMS f)
    (x : X → ℝ) (hx : InUnitCube x) (b : ℝ) (hb : 0 < b) (hfb : ∀ j : X, f {j} ≤ b)
    (ρ : (X → ℝ) → X × X) (hρ : IsChoiceRule ρ) :
    (∀ j : X, prob (alg1Law f ρ x) (fun S => j ∈ S) = x j) ∧
    Real.log (max b (F f x / C)) ≤
      expect (alg1Law f ρ x) (fun S => Real.log (max (f S) b)) ∧
    ∀ o ∈ (alg1Run f ρ x).support, o.2 = true := by sorry

end ForestRoundingNSW.Rounding
