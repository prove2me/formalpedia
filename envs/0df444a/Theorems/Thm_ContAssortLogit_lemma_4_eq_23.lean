-- Prove2me | Theorems.Thm_ContAssortLogit_lemma_4_eq_23
-- name    : ContAssortLogit.lemma_4_eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:16.929704+00:00
-- url     : https://prove2.me/theorems/a00d1b22-54c6-47d0-9e89-23982c9bfcea
-- title:
--   Lemma 4, (23), p.35 — the drift inequality $(\varrho-\varrho^*)(h(\varrho)-\varrho)\le-(\varrho-\varrho^*)^2/(1+\overline v)$
-- statement:
--   Let $w$ be a revenue function and $v\in\mathcal V(\underline v,\overline v,D)$, with $\overline v$ the upper bound of the class. Then for every $\varrho\in[0,1]$,
--   $$(\varrho-\varrho^*)\,(h(\varrho)-\varrho)\le-\frac{1}{1+\overline v}\,(\varrho-\varrho^*)^2.\tag{23}$$
--
--   The mean update direction $h(\varrho)-\varrho$ of SAP points towards $\varrho^*$ with a strength proportional to the distance; this drives the mean-square recursion (25).
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, Lemma 4, (23), p.35

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- **Lemma 4, inequality (23)** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, p.35): for
`ϱ ∈ [0, 1]`, `(ϱ − ϱ*)(h(ϱ) − ϱ) ≤ −(1 / (1 + v̄)) (ϱ − ϱ*)²`, where `v̄` is the upper bound of the
class `𝒱`. -/
theorem lemma_4_eq_23 (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) :
    ∀ ϱ ∈ Icc (0 : ℝ) 1,
      (ϱ - optRev w v) * (hfun w v ϱ - ϱ) ≤ -(1 / (1 + vhi)) * (ϱ - optRev w v) ^ 2 := by sorry

end ContAssortLogit
