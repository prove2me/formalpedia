-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_lemma_3_2
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:28:53.843984+00:00
-- url     : https://prove2.me/theorems/56ca5ad4-3e87-4125-bbea-40334ba752a0
-- title:
--   Lemma 3.2 — the improper tree learner errs by more than ε with probability at most e^{−mε}
-- statement:
--   Let $X$, $Y$, $\mathcal H=\{h_{d,b,u}\}$ be the construction of §3.1 and $A$ the improper learner of p. 17 (it outputs $h_{d,b,u}$ when a private label $\alpha_{d,b,u}$ appears, and otherwise reconstructs all blocks above a deepest example). For every target $h\in\mathcal H$, every probability distribution $D$ on $X$, every $\varepsilon\in(0,1)$ and every sample size $m\ge1$,
--   $$\Pr_{S\sim D^m}\big[L_D(A(S),h)>\varepsilon\big]\le e^{-m\varepsilon},$$
--   where $S$ consists of $m$ i.i.d. draws from $D$ labeled by $h$ and $L_D(g,h)=\Pr_{x\sim D}[g(x)\ne h(x)]$.
--
--   This is the positive half of Theorem 3.1: with $n_A(\varepsilon,\delta)=\max(1,\lceil\ln(1/\delta)/\varepsilon\rceil)$ it shows that $A$ PAC learns $\mathcal H$, so $\mathcal H$ is learnable.
--
--   **Formalization Note.** `failProb refLearner h D m ε` is the $D^m$-measure of the set of point tuples whose labeled sample makes $A$ err with $D$-probability $>\varepsilon$; the bound is `ENNReal.ofReal (Real.exp (-(m * ε)))`.
--
--   Differences from the source:
--   - encoding: the learner A of p. 17, defined on samples drawn from a target, with "any" deepest example → `refLearner`, total on every finite sample: first private label in sample order, first deepest example in sample order, constant 0 on the empty sample; reason: §2 requires a learner on all of (X × Y)^{<ω}; the lemma evaluates A only on samples labeled by a target in H, where every choice gives the same output
--   - encoding: distribution D on X → probability measure on X with σ-algebra ⊤ (every subset measurable); reason: X is countable, so these are exactly the distributions on X
--   - encoding: P[L_D(A(S), h) > ε] ≤ e^{−mε} → `Measure.pi` product measure of {xs | ofReal ε < D{x | A(S)(x) ≠ h(x)}} ≤ ofReal (exp (−mε)) in ℝ≥0∞, S = xs labeled by h; reason: Lean convention; same numbers
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 17, Lemma 3.2

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

open MeasureTheory

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-- Lemma 3.2 (p. 17): for every target `h ∈ H`, every probability measure `D` on `X`,
every `ε ∈ (0, 1)` and every sample size `m ≥ 1`, the learner `A` fails with probability
`P[L_D(A(S), h) > ε] ≤ e^{−mε}`. -/
theorem lemma_3_2 (h : Pt → Label) (hh : h ∈ H) (D : @Measure Pt ⊤)
    (hD : @IsProbabilityMeasure Pt ⊤ D) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (m : ℕ)
    (hm : 1 ≤ m) :
    failProb refLearner h D m ε ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * ε))) := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
