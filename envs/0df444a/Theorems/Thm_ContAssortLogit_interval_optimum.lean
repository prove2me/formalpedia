-- Prove2me | Theorems.Thm_ContAssortLogit_interval_optimum
-- name    : ContAssortLogit.interval_optimum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:10.470529+00:00
-- url     : https://prove2.me/theorems/278d80c5-537c-49b0-8a1b-8644b835ad2c
-- title:
--   §4.1, p.10 — the optimal assortment is an interval $[w^{-1}(\varrho),1]$
-- statement:
--   Let $w$ be a revenue function and $v\in\mathcal V(\underline v,\overline v,D)$. Then the maximum of the expected revenue over all feasible assortments is attained, it is also attained by an interval of the form $[w^{-1}(\varrho),1]$, and
--   $$\max\{r(S,v):S\in\mathcal S\}=\max\{r([w^{-1}(\varrho),1],v):\varrho\in[0,1]\}.$$
--
--   This is the continuous counterpart of the revenue-ordered optimality of MNL assortments: the seller should offer every product whose revenue is above a threshold, which reduces the search over all Borel sets to a one-dimensional search.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, §4.1, p.10, display after (4)

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- **The optimal assortment is an interval** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4,
§4.1, p.10): `max{r(S, v) : S ∈ 𝒮} = max{r([w⁻¹(ϱ), 1], v) : ϱ ∈ [0, 1]}`, both maxima attained.
In Lean: `ϱ* = optRev w v` is the greatest element of `{r(S, v) : S ∈ 𝒮}` and also the greatest
element of `{r([w⁻¹(ϱ), 1], v) : ϱ ∈ [0, 1]}`.

**Formalization Note.** `𝒮` is the set of Borel subsets of `[0, 1]` (case `c = 1`); `w⁻¹ := 1`
above `w(1)` (see `winv`). -/
theorem interval_optimum (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) :
    IsGreatest (rev w v '' Assortments) (optRev w v) ∧
      IsGreatest ((fun ϱ => rev w v (Icc (winv w ϱ) 1)) '' Icc (0 : ℝ) 1) (optRev w v) := by sorry

end ContAssortLogit
