-- Prove2me | Theorems.Thm_ContAssortLogit_lemma_4_fixed_point
-- name    : ContAssortLogit.lemma_4_fixed_point
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:02.633514+00:00
-- url     : https://prove2.me/theorems/2f5293f7-e09a-45c4-8945-00579abda602
-- title:
--   Lemma 4 (first claim), p.35 — $\varrho^*$ is a fixed point of $h$
-- statement:
--   Let $w$ be a revenue function and $v\in\mathcal V(\underline v,\overline v,D)$, let $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ and $h(\varrho)=r([w^{-1}(\varrho),1],v)$. Then
--   $$h(\varrho^*)=\varrho^*.$$
--
--   The optimal revenue solves the fixed-point equation $h(\varrho)=\varrho$; this is why a Robbins–Monro scheme on noisy observations of $h$ can find it.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, Lemma 4, p.35

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- **Lemma 4, first claim** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, p.35):
`h(ϱ*) = ϱ*`, where `h(ϱ) = r([w⁻¹(ϱ), 1], v)` and `ϱ* = max{r(S, v) : S ∈ 𝒮}`. -/
theorem lemma_4_fixed_point (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) :
    hfun w v (optRev w v) = optRev w v := by sorry

end ContAssortLogit
