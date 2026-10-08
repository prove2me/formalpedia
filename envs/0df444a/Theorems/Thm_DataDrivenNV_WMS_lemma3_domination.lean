-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_lemma3_domination
-- name    : DataDrivenNV.WMS.lemma3_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:06.785977+00:00
-- url     : https://prove2.me/theorems/bdc6f2ab-40a8-47a5-9456-211e30480027
-- title:
--   Lemma 3 (Domination Lemma), p. 15 — f₁ ≤ f₂ on {f₂ > 0} = interval ∋ t and F₁(t) = F₂(t) imply Δ₁(t) ≥ Δ₂(t)
-- statement:
--   Let $f_1,f_2$ be probability densities on $\mathbb R$ with cdfs $F_1,F_2$ and absolute mean spreads $\Delta_1,\Delta_2$, where $\Delta_i(t)=E(D_i\mid D_i\ge t)-E(D_i\mid D_i\le t)$. Let $t\in\mathbb R$ and suppose:
--
--   1. $f_1(x)\le f_2(x)$ for every $x$ with $f_2(x)>0$;
--   2. $F_1(t)=F_2(t)$, and $0<F_1(t)<1$;
--   3. $x f_1(x)$ and $x f_2(x)$ are integrable;
--   4. there are $l\le t\le u$ such that $f_2=0$ outside $[l,u]$ and $f_2>0$ on $(l,u)$.
--
--   Then
--   $$\Delta_1(t)\ \ge\ \Delta_2(t).$$
--
--   The lemma compares the dispersion around $t$ of two laws: a density that dominates another on its own support, with the same mass to the left of $t$, is more concentrated around $t$. It is the step of Proposition 1 that turns the envelope of Lemma 2 into optimality of (12).
--
--   **Formalization Note** As printed (without hypothesis 4) the lemma is false: with $f_2=\tfrac12$ on $[-1,0]\cup[1,2]$, $f_1=\tfrac12$ on $[-1,1]$ and $t=0$, the other hypotheses hold but $\Delta_1(0)=1<\Delta_2(0)=2$; the proof's step "$F_1(x)\le F_2(x)$ for all $x\ge t$" fails on the gap $(0,1)$. Hypothesis 4 (the support of $f_2$ is an interval containing $t$) is exactly the situation in which the paper applies the lemma, to $f_2=\tilde f$ of (12), and with it the printed proof goes through. Hypotheses 2 (the part $0<F_1(t)<1$) and 3 are the standing conditions under which the conditional means of Definition 1 exist.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 15, Lemma 3 (Domination Lemma); proof EC.5, p. ec9

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Lemma 3 (Domination Lemma)** (p. 15), with the support of `f₂` an interval `[l, u] ∋ t`:
if `f₁ ≤ f₂` wherever `f₂ > 0` and `F₁(t) = F₂(t) ∈ (0, 1)`, then `Δ₂(t) ≤ Δ₁(t)`.
The interval hypothesis is needed: as printed the lemma fails when `{f₂ > 0}` has a gap
to the right or left of `t`. -/
theorem lemma3_domination (f₁ f₂ : ℝ → ℝ) (h₁ : IsPdf f₁) (h₂ : IsPdf f₂) (t : ℝ)
    (hle : ∀ x, 0 < f₂ x → f₁ x ≤ f₂ x)
    (hF : cdfOf f₁ t = cdfOf f₂ t) (hF0 : 0 < cdfOf f₁ t) (hF1 : cdfOf f₁ t < 1)
    (hm₁ : Integrable (fun x => x * f₁ x)) (hm₂ : Integrable (fun x => x * f₂ x))
    (l u : ℝ) (hlt : l ≤ t) (htu : t ≤ u)
    (hout : ∀ x, x < l ∨ u < x → f₂ x = 0) (hin : ∀ x, l < x → x < u → 0 < f₂ x) :
    ams f₂ t ≤ ams f₁ t := by sorry

end DataDrivenNV.WMS
