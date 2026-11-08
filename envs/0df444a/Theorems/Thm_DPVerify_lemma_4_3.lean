-- Prove2me | Theorems.Thm_DPVerify_lemma_4_3
-- name    : DPVerify.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:01.110111+00:00
-- url     : https://prove2.me/theorems/56447013-3c4e-4f63-82e5-d510bec264c6
-- title:
--   Lemma 4.3 — max-information $\le k$ gives $(\hat\beta,2k,\hat\beta)$-one-way perfect generalization (corrected: countably generated output σ-algebra)
-- statement:
--   This is Lemma 3.14 of Bun, Gaboardi, Hopkins, Impagliazzo, Lei, Pitassi, Sivakumar and Sorrell [BGH+23], as restated in the paper.
--
--   Let $k>0$, $\beta\in(0,1)$ and
--
--   $$
--   \hat\beta=\sqrt{\frac{\beta}{1-2^{-k}}}.
--   $$
--
--   Let $\mathcal A:\mathcal X^m\to\mathcal Y$ be a randomized algorithm whose output space has a countably generated σ-algebra, and let $D$ be a distribution on $\mathcal X$. If $S\sim D^m$ satisfies $I^\beta_\infty(S;\mathcal A(S))\le k$, then $\mathcal A$ satisfies the $(\hat\beta,2k,\hat\beta)$-one-way perfect generalization condition at $D$: there is a distribution $\mathrm{Sim}_D$ on $\mathcal Y$ such that, with probability at least $1-\hat\beta$ over $S\sim D^m$, every measurable $O\subseteq\mathcal Y$ satisfies
--
--   $$
--   \Pr[\mathcal A(S)\in O]\le e^{2k}\Pr_{\mathrm{Sim}_D}[O]+\hat\beta .
--   $$
--
--   This is the second step of the transfer from differential privacy to replicability.
--
--   Differences from the source:
--   - correction: an arbitrary output space $\mathcal Y$ → the σ-algebra of $\mathcal Y$ is countably generated (every countable or standard Borel space qualifies); reason: for an arbitrary measurable space the statement is false: with $\mathcal X=\mathcal Y=[0,1]$, $m=1$, $D$ uniform, $\mathcal A(S)=S$ and the countable–cocountable σ-algebra on $\mathcal Y$, the joint and product laws agree on every measurable set, so $I^\beta_\infty\le k$ holds for $\beta=0.01$, $k=1$, while the conclusion with $O=\{S\}$ would give $\mathrm{Sim}_D(\{S\})\ge(1-\hat\beta)e^{-2}>0$ for uncountably many $S$; Definition 2.4 quantifies over every output set $O\subseteq\mathcal Y$, which presumes such a space
--   - reading: for every distribution $D$, if $I^\beta_\infty(S;\mathcal A(S))\le k$ for $S\sim D^m$, then $\mathcal A$ is one-way perfectly generalizing (Definition 2.4 quantifies over every distribution) → the hypothesis at $D$ gives the one-way perfect generalization condition at the same $D$; reason: read literally the sentence is false: for a point mass $D$ the sample is constant and the hypothesis holds for every $\mathcal A$, while the identity algorithm is not one-way perfectly generalizing at the uniform distribution on a large finite set; the per-distribution form is what Corollary 4.5 uses
--   - reading: $\log$ in Definition 2.3 → natural logarithm in the hypothesis; $2^{-k}$ in $\hat\beta$ kept as printed; reason: Definition 2.3 does not fix the base; Definitions 2.2 and 2.4 use $e^\varepsilon$; a base-2 bound implies the natural one, so this reading assumes less
--   - encoding: with probability at least $1-\hat\beta$ over $S\sim D^m$ → a measurable set of samples of $D^m$-probability at least $1-\hat\beta$ on which the inequality holds for every measurable $O$; reason: makes the probability defined
--   - encoding: an algorithm $\mathcal A:\mathcal X^m\to\mathcal Y$, a distribution $D$ → a randomized algorithm with explicit coins, jointly measurable, between measurable spaces; $D$ a probability measure; reason: Lean representation; makes every probability defined
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Lemma 4.3, p.18 (PDF p.21); Definitions 2.3–2.4, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_MaxInfoLE
import Definitions.Def_DPVerify_IsOWPGAt

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- Lemma 4.3 (Lemma 3.14 of [BGH+23]; Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.18 = PDF p.21): bounded max-information gives one-way
perfect generalization. Let `k > 0`, `β ∈ (0, 1)` and `β̂ = √(β / (1 − 2^{−k}))`. If
`I^β_∞(S; A(S)) ≤ k` for `S ∼ D^m`, then `A` satisfies the `(β̂, 2k, β̂)`-one-way perfect
generalization condition at `D`.

**Formalization Note** The statement is per distribution: the hypothesis at `D` gives the
conclusion at the same `D`. Read with "`A` is OWPG" quantifying over every distribution, the
printed sentence is false (with `D` a point mass the hypothesis holds for every `A`). The
max-information uses the natural logarithm; `β̂` keeps the printed `2^{−k}`.

Correction: the output σ-algebra is countably generated (every countable or standard Borel output
space qualifies). For an arbitrary measurable space the statement is false: take `X = Y = [0, 1]`,
`m = 1`, `D` uniform, `A(S) = S`, and give `Y` the countable–cocountable σ-algebra. Then the joint
law and the product law agree on every measurable set, so `I^β_∞ ≤ k` holds for every `β, k > 0`,
but `Pr[A(S) ∈ {S}] = 1 ≤ e^{2k} Sim_D({S}) + β̂` would force `Sim_D({S}) > 0` for uncountably many
`S` when `β̂ < 1`. -/
theorem lemma_4_3 (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (m : ℕ) (k β : ℝ)
    (hk : 0 < k) (hβ0 : 0 < β) (hβ1 : β < 1) (A : RandAlg X Y m) (D : ProbabilityMeasure X)
    (h : MaxInfoLE A D β k) :
    IsOWPGAt A D (Real.sqrt (β / (1 - (2 : ℝ) ^ (-k)))) (2 * k)
      (Real.sqrt (β / (1 - (2 : ℝ) ^ (-k)))) := by sorry

end DPVerify
