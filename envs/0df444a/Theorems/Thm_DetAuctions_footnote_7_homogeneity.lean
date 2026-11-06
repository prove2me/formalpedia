-- Prove2me | Theorems.Thm_DetAuctions_footnote_7_homogeneity
-- name    : DetAuctions.footnote_7_homogeneity
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:46.062356+00:00
-- url     : https://prove2.me/theorems/8294e0ed-ef22-4fab-9810-92bba2802dc4
-- title:
--   Footnote 7 (a) — positive homogeneity $\mathsf{REV}(\lambda X)=\lambda\,\mathsf{REV}(X)$
-- statement:
--   For every random vector $X$ of item values in $\mathbb R_+^m$ (no independence assumed) and every scalar $\lambda>0$,
--   $$\mathsf{REV}(\lambda\cdot X)=\lambda\cdot\mathsf{REV}(X).$$
--
--   This makes the normalization of values to $[0,1]$ a matter of scaling.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. On the value space $V=\mathbb R_+^m$ one has $\lambda V=V$.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], footnote 7, p.9 (pdf p.11)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Footnote 7 (a), positive homogeneity of the optimal revenue**: `REV(λ·X) = λ·REV(X)` for
every scalar `λ > 0`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), footnote 7, p.9: "it is easy to see that the optimal revenue operator (2) is positive
homogeneous, i.e. REV_{λ·V}(λ · X) = λ · REV_V(X) for any scalar λ > 0".

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
The value space is `V = ℝ₊^m`, so `λ·V = V`. No independence is assumed, as in the footnote. -/
theorem footnote_7_homogeneity {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0))
    [IsProbabilityMeasure μ] (lam : ℝ≥0) (hlam : 0 < lam) :
    Rev (μ.map (fun x => lam • x)) = (lam : ℝ≥0∞) * Rev μ := by sorry

end DetAuctions
