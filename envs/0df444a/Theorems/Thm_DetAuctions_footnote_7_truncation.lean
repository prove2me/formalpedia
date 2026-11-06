-- Prove2me | Theorems.Thm_DetAuctions_footnote_7_truncation
-- name    : DetAuctions.footnote_7_truncation
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:49.733025+00:00
-- url     : https://prove2.me/theorems/6a3157e3-1ea5-46d1-9663-620adc016009
-- title:
--   Footnote 7 (b) — truncation: $\mathsf{REV}(X)\le\sup_H\mathsf{REV}(\min\{X,H\})$
-- statement:
--   For every random vector $X$ of item values in $[0,\infty)^m$ (no independence assumed), with $\tilde X^H_j=\min\{X_j,H\}$ the values truncated at $H$,
--   $$\mathsf{REV}(X)\le\sup_{H\ge0}\mathsf{REV}\big(\tilde X^H\big).$$
--
--   Since truncation does not increase $\mathsf{SREV}$ or $\mathsf{BREV}$, any bound $\mathsf{REV}\le c_1\mathsf{SREV}+c_2\mathsf{BREV}$ proved for bounded values transfers to unbounded ones: this is the footnote's "taking the limit as $H\to\infty$, one recovers the appropriate approximation".
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. Neither equality nor a limit of $\mathsf{REV}(\tilde X^H)$ is claimed (revenue is not monotone).
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - reading: "truncate to X̃_j = min{X_j, H} … taking the limit as H → ∞, one recovers the appropriate approximation" → Rev μ ≤ ⨆ H, Rev (law of min{X, H}); reason: the footnote gives no formula; this is the inequality that transfers the paper's upper bounds from bounded to unbounded values
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], footnote 7, p.9 (pdf p.11)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Footnote 7 (b), truncation of unbounded values**: the optimal revenue of a value law on
`[0, ∞)^m` is at most the supremum over `H` of the optimal revenues of the truncated values
`X̃ⱼ = min{Xⱼ, H}`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), footnote 7, p.9: "starting from a value distribution Xj, j ∈ [m], defined over [0, ∞), one
can truncate to X̃j = min{Xj, H} and perform our revenue analysis on the new, truncated
instance. Then, taking the limit as H → ∞, one recovers the appropriate approximation".

**Formalization Note** Reading: the footnote gives no formula; "recovers the appropriate
approximation" is read as `REV(X) ≤ sup_H REV(X ∧ H)`, the inequality that transfers an upper
bound `REV ≤ c·(…SREV, BREV…)` proved for bounded values to unbounded ones (truncation does not
increase `SREV` or `BREV`). Neither equality nor a limit is claimed: revenue is not monotone.
The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`. No independence is assumed. -/
theorem footnote_7_truncation {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0))
    [IsProbabilityMeasure μ] :
    Rev μ ≤ ⨆ H : ℝ≥0, Rev (μ.map (fun x j => min (x j) H)) := by sorry

end DetAuctions
