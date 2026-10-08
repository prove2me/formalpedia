-- Prove2me | Theorems.Thm_DataDrivenNV_LRS_lrsSet_subset_epsOptimal
-- name    : DataDrivenNV.LRS.lrsSet_subset_epsOptimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:42.665817+00:00
-- url     : https://prove2.me/theorems/5acb7bdd-a0d7-4a98-9bf5-2ee6103ee67f
-- title:
--   (3), p. 8 — for 0 < ε ≤ 1, every q in S^LRS_ε is ε-optimal: S^LRS_ε ⊆ S_ε
-- statement:
--   Let $D$ have law $\mu$ on $\mathbb R$ with $\mathbb E|D|<\infty$, let $b,h>0$, and let $C$, $q^*$ and the interval
--   $$S^{LRS}_\epsilon=\Big\{q:\partial_-C(q)\le\tfrac\epsilon3\min(b,h)\text{ and }\partial_+C(q)\ge-\tfrac\epsilon3\min(b,h)\Big\}$$
--   be as in display (3). Then for $0<\epsilon\le1$,
--   $$S^{LRS}_\epsilon\subseteq S_\epsilon=\{q : C(q)\le(1+\epsilon)\,C(q^*)\}.$$
--
--   This inclusion, due to Levi, Roundy and Shmoys (2007) and quoted in §2.1, converts a bound on the one-sided derivatives of $C$ at a point into a bound on its relative regret. Combined with Proposition EC.1 it yields Theorem 2.
--
--   **Formalization Note** The paper states the inclusion for every $\epsilon>0$; it is restricted here to $\epsilon\le1$, where it holds. For large $\epsilon$ it fails: with $b=h$ and $\epsilon\ge3$ both conditions in (3) are vacuous (the derivatives lie in $[-b,h]$), so $S^{LRS}_\epsilon=\mathbb R$; for $D\in\{0,M\}$ with $\Pr(D=M)=0.005$ one has $q^*=0$, $C(0)=0.005M$ and $C(M)=0.995M$, a relative regret of $199-1=198$. The hypothesis $\mathbb E|D|<\infty$ makes $C$ a genuine expectation.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 8, §2.1, display (3) and the sentence following it (cited from Levi, Roundy & Shmoys 2007)

import Mathlib
import Definitions.Def_DataDrivenNV_LRS_Setting

open MeasureTheory ProbabilityTheory

namespace DataDrivenNV.LRS

/-- Display (3), §2.1, p. 8 (Levi, Roundy & Shmoys 2007): for `0 < ε ≤ 1` every order quantity in
the LRS interval `S^LRS_ε` is `ε`-optimal, `S^LRS_ε ⊆ S_ε`. The restriction `ε ≤ 1` is needed:
for `b = h` and `ε ≥ 3` the interval is all of `ℝ`. -/
theorem lrsSet_subset_epsOptimal (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    lrsSet μ b h ε ⊆ {q | IsEpsOptimal μ b h ε q} := by sorry

end DataDrivenNV.LRS
