-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_4_6
-- name    : BLTCounting.AccuracySpace.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:39.283833+00:00
-- url     : https://prove2.me/theorems/5687107a-2b13-49d1-84ea-a37fbc40da40
-- title:
--   Operator-norm approximation, uniformly in $\eta$
-- statement:
--   Fix $\varepsilon\in(0,1/2)$. Let $h$, $R$, $K$ be computed from $m$ and $\eta$ as in equation (28), with $L=\log m$ and $A=\log(1/\eta)$, and let $F(f)$ and $V_h$ be the resulting $K\times K$ matrices. Then
--   $$\|F(f)-V_h\|_2=o(\eta)\qquad(m\to\infty),$$
--   uniformly over the range $0<A\le(1/2-\varepsilon)L$: for every $\delta>0$ there is $m_0(\varepsilon,\delta)$ with $\|F(f)-V_h\|_2\le\delta\eta$ for all $m\ge m_0$ and all $\eta$ in the range.
--
--   This transfers spectral information from the Toeplitz matrix $V_h$ to $F(f)$, for $\eta$ that may vary with $m$.
--
--   Differences from the source:
--   - reading: $\|F(f)-V_h\|_2\le o(\eta)$ → for every $\delta>0$ a threshold $m_0(\varepsilon,\delta)$, uniform over admissible $\eta$; reason: the source applies the bound with $\eta$ varying with $n$, so the uniform reading is the one its proof of Theorem 1.2 uses and proves
--   - generalization: the standing range $a_*\le A\le(1/2-\varepsilon)L$ of Section 4 → the range $0<A\le(1/2-\varepsilon)L$, with $m_0$ independent of $a_*$; reason: every $a_*>0$ gives a subrange of it; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 4.6, printed p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Definitions.Def_BLTCounting_AccuracySpace_Sequences
import Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks

namespace BLTCounting.AccuracySpace

/-- Lemma 4.6, PDF p. 29: fix `ε ∈ (0, 1/2)`. With Section 4's parameters `h`, `R`, `K` computed from
`m` and `η`, `‖F(f) - V_h‖₂ = o(η)` as `m → ∞`, uniformly over all `η` with
`0 < log(1/η) ≤ (1/2 - ε) log m`: for every `δ > 0` there is `m₀(ε, δ)` such that the bound `δη` holds
for all such pairs `(m, η)` with `m ≥ m₀`. -/
theorem lemma_4_6 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ η : ℝ, 0 < η → 0 < Real.log (1 / η) →
      Real.log (1 / η) ≤ (1 / 2 - ε) * Real.log m →
      specNorm (blockCompression (sectionR m η) (sectionH m η) (sectionK m η) sqrtSeq -
          rescaledToeplitz (sectionK m η) (sectionH m η)) ≤ δ * η := by sorry

end BLTCounting.AccuracySpace
