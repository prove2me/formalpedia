-- Prove2me | Theorems.Thm_AltRegret_Supplement_theorem_10
-- name    : AltRegret.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:12:46.125278+00:00
-- url     : https://prove2.me/theorems/2bf8aa76-e765-4f2d-a0c4-4dfcf34349c7
-- title:
--   Theorem 10 — linear dimension dependence is necessary
-- statement:
--   Let $d\ge2$, $T\ge16$, $r=1/\sqrt d$, and let $X$ be the product of $\lfloor d/2\rfloor$ copies of $rB_2(1)$ together with one interval $[-r,r]$ when $d$ is odd. For every possibly randomized causal online algorithm on $X$, there is a deterministic oblivious sequence of continuous convex losses $f_1,\ldots,f_T:X\to[0,1]$ such that
--   $$
--   \mathbb E_A[\operatorname{Reg}_{\mathrm{Alt}}^T]\ge\frac{mK}{125},
--   \qquad
--   m=\min\left\{\left\lfloor\frac d2\right\rfloor,\left\lfloor\frac T{16}\right\rfloor\right\},
--   \quad
--   K=\left\lfloor\log_{16}\left\lfloor\frac Tm\right\rfloor\right\rfloor.
--   $$
--   In particular this yields the paper's $\Omega(d\log(1+T/d))$ lower bound.
--
--   The statement uses the paper's specific body and preserves every floor and the exact constant.
--
--   Differences from the source:
--   - encoding: the product body X is displayed as a Cartesian product → coordinate-pair inequalities define the same product, with the last coordinate constrained to [−r,r] when d is odd; reason: this is the literal coordinate membership test for the displayed body
--   - encoding: a possibly randomized online algorithm A → a measurable causal map from past losses and a private seed with an arbitrary probability law; reason: the deterministic loss sequence is existential outside the seed, preserving obliviousness and the expectation convention
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 10, p.15

import Mathlib
import Definitions.Def_AltRegret_Supplement_OnlineAlgorithm
import Definitions.Def_AltRegret_Supplement_productBody

open MeasureTheory

namespace AltRegret.Supplement

/-- **Theorem 10 (Linear dimension dependence is necessary).** Tao–Zheng,
*Optimal Alternating Regret for Online Learning and Games*, arXiv:2608.24731, Theorem 10,
p.15. On the paper's product body `X ⊆ B_d(1)`, every randomized online algorithm has a
deterministic oblivious continuous convex loss sequence forcing expected alternating regret
at least `mK/125`, with the exact floor definitions of `m` and `K`.

**Formalization Note.** `productBody d` is exactly the product of `⌊d/2⌋` copies of
`(1/√d) B₂(1)` and, for odd `d`, the interval `[-1/√d,1/√d]`. -/
theorem theorem_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 2 ≤ d) (A : OnlineAlgorithm Ω d)
    (hA : IsOnlineAlgorithmOn (productBody d) A)
    (T : ℕ) (hT : 16 ≤ T) :
    ∃ f : ℕ → Point d → ℝ,
      (∀ t, 1 ≤ t → t ≤ T →
        ContinuousOn (f t) (productBody d) ∧
        ConvexOn ℝ (productBody d) (f t) ∧
        ∀ u ∈ productBody d, f t u ∈ Set.Icc (0 : ℝ) 1) ∧
      ((lowerBlockCount d T * lowerLogCount d T : ℕ) : ℝ) / 125 ≤
        expectedWorstAltRegret P (productBody d) A f T := by sorry

end AltRegret.Supplement
