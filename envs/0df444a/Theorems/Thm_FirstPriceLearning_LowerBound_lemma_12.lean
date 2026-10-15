-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_lemma_12
-- name    : FirstPriceLearning.LowerBound.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:29.951163+00:00
-- url     : https://prove2.me/theorems/d49f1203-2c83-4d19-9512-c8ff04e0e35a
-- title:
--   Lemma 12, p. 36 — $1-\|P-Q\|_{\mathrm{TV}}\ge\tfrac12\exp(-(D_{\mathrm{KL}}(P\|Q)+D_{\mathrm{KL}}(Q\|P))/2)$
-- statement:
--   Let $P$ and $Q$ be two probability measures on the same measurable space. Then
--
--   $$
--   1-\|P-Q\|_{\mathrm{TV}}\ \ge\ \frac12\exp\Bigl(-\frac{D_{\mathrm{KL}}(P\|Q)+D_{\mathrm{KL}}(Q\|P)}{2}\Bigr),
--   $$
--
--   with $\exp(-\infty)=0$, so the right-hand side is $0$ when either divergence is infinite.
--
--   This symmetrised form of the Bretagnolle–Huber inequality converts a bound on the Kullback–Leibler divergences between two hypotheses into a lower bound on the overlap $1-\|P-Q\|_{\mathrm{TV}}=\int\min\{dP,dQ\}$, which is what Le Cam's two-point method needs.
--
--   **Formalization Note** The divergences are Mathlib's `klDiv`, valued in $[0,\infty]$. The right-hand side is written as $0$ when either divergence is $\infty$ and as $\tfrac12\exp(-(D_{\mathrm{KL}}(P\|Q)+D_{\mathrm{KL}}(Q\|P))/2)$ with real-valued divergences otherwise; this avoids Lean's convention that $\infty$ converts to the real number $0$, which would make the statement false for mutually singular $P,Q$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 36, App. A, Lemma 12

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_TVDist

open MeasureTheory InformationTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. A, Lemma 12, p. 36: for probability measures `P, Q` on the same space,
`1 − ‖P − Q‖_TV ≥ (1/2) exp(−(D_KL(P‖Q) + D_KL(Q‖P))/2)`. The right side is read with
`exp(−∞) = 0`: it is `0` when either divergence is infinite. -/
theorem lemma_12 {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (if klDiv P Q = ⊤ ∨ klDiv Q P = ⊤ then (0 : ℝ)
      else 1 / 2 * Real.exp (-((klDiv P Q).toReal + (klDiv Q P).toReal) / 2)) ≤
      1 - tvDist P Q := by sorry

end FirstPriceLearning.LowerBound
