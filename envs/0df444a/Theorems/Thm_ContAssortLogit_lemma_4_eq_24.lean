-- Prove2me | Theorems.Thm_ContAssortLogit_lemma_4_eq_24
-- name    : ContAssortLogit.lemma_4_eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:17.077416+00:00
-- url     : https://prove2.me/theorems/c26545ff-7d06-4089-8080-638281fe0cbd
-- title:
--   Lemma 4, (24), p.35 — $h(\varrho^*)-h(\varrho)\le C(\varrho-\varrho^*)^2$ with a universal $C$
-- statement:
--   Let $w$ be a revenue function and $\overline v>\underline v>0$ class parameters as in Assumption 1, with derivative bound $D$. There is a constant $C>0$ such that for every $v\in\mathcal V(\underline v,\overline v,D)$ and every $\varrho\in[0,1]$,
--   $$h(\varrho^*)-h(\varrho)\le C\,(\varrho-\varrho^*)^2.\tag{24}$$
--
--   The revenue lost by offering $[w^{-1}(\varrho),1]$ instead of the optimal assortment is quadratic in the error of $\varrho$; this turns the mean-square rate $\delta_t=O(1/t)$ into logarithmic regret.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
--   - reading: a universal constant $C>0$ → $C$ chosen after $w,\underline v,\overline v,D$ and before $v\in\mathcal V$ and $\varrho$; reason: 'universal' is uniformity over the class, which Theorem 1's worst-case bound needs; the paper's $C=\overline v/k_w+C_0/(2k_w^2)$ (p.39) depends only on these
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, Lemma 4, (24), p.35 (constant C on p.39)

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- **Lemma 4, inequality (24)** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, p.35): there is
a universal constant `C > 0` such that `h(ϱ*) − h(ϱ) ≤ C (ϱ − ϱ*)²` for all `ϱ ∈ [0, 1]`.

**Formalization Note.** "Universal" is read as uniform over the class: `C` is chosen after `w` and
the class parameters `v̲, v̄, D`, and before `v ∈ 𝒱` (the paper's `C = v̄/k_w + C₀/(2k_w²)`, p.39,
depends only on these). -/
theorem lemma_4_eq_24 (w : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ → ℝ, InClass vlo vhi D v →
      ∀ ϱ ∈ Icc (0 : ℝ) 1,
        hfun w v (optRev w v) - hfun w v ϱ ≤ C * (ϱ - optRev w v) ^ 2 := by sorry

end ContAssortLogit
