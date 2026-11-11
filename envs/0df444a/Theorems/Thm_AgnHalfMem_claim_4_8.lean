-- Prove2me | Theorems.Thm_AgnHalfMem_claim_4_8
-- name    : AgnHalfMem.claim_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:54.139123+00:00
-- url     : https://prove2.me/theorems/48bbbbb3-e58d-48c2-a194-074e6663f8ca
-- title:
--   Claim 4.8 — a random sine correlates with its halfspace with probability $\ge 1/(16\tau)$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with finite non-zero variance, half-variance radius $L_\mu$, and normalized difference law $\mu'$. Let $s$ be a positive integer with $s\ge 64L_\mu^2$ and let $\tau\ge 8$. For $v\in\mathbb R^s$ write $f_v(z)=\sin(\tau\langle v,z\rangle)$. Then
--   $$
--   \Pr_{v\sim N(0,\frac1s I_s)}\Big[\ \mathbb E_{z\sim\mu'^{\otimes s}}\big[f_v(z)\,\mathrm{sign}(\langle v,z\rangle)\big]\ \ge\ \frac1{16\tau}\Big]\ \ge\ \frac{1}{16\tau}.
--   $$
--
--   The claim supplies, inside the proof of Lemma 4.7, many directions $v$ whose sine function has correlation $\Omega(1/\tau)$ with the halfspace $\mathrm{sign}(\langle v,\cdot\rangle)$.
--
--   Differences from the source:
--   - generalization: claim stated inside the proof of Lemma 4.7, under that lemma's context (L_µ ≤ c₂√d, τ ≥ c₁, s = ⌊d/2⌋) → every µ with finite non-zero variance, every s with 64·L_µ² ≤ s, every τ ≥ 8; reason: these are the only conditions the proof uses ("provided that s ≥ 64L²", "For τ ≥ 8"); the lemma's context implies them for c₁ ≥ 8 and c₂ small
--   - encoding: N(0, I_s/s), µ′^{⊗s}, sign → gaussVec s, Measure.pi of diffLaw μ, sgn ∘ signB with sign(0) = +1; reason: Lean conventions; same instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim 4.8, p.14 (proof pp.14–15)

import Mathlib
import Definitions.Def_AgnHalfMem_halfspace
import Definitions.Def_AgnHalfMem_halfVarRadius
import Definitions.Def_AgnHalfMem_sineFn

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **Claim 4.8 (a random sine correlates with its halfspace).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Claim 4.8, p.14:
"Pr_{v∼N(0, (1/s) I_s)}[E_{z∼µ′^{⊗s}}[f_v(z) sign(⟨v, z⟩)] ≥ 1/(16τ)] ≥ 1/(16τ)."

For every probability measure `μ` with finite non-zero variance, every `s` with `s ≥ 64 L_μ²` and
every `τ ≥ 8`, a vector `v ∼ N(0, I_s/s)` satisfies
`E_{z∼µ′^{⊗s}}[sin(τ⟨v, z⟩) sign(⟨v, z⟩)] ≥ 1/(16τ)` with probability at least `1/(16τ)`.

**Formalization Note.** The context of the claim inside the proof of Lemma 4.7 is made explicit:
`s ≥ 64 L_μ²` and `τ ≥ 8` are the two conditions its proof uses ("provided that s ≥ 64L²",
"For τ ≥ 8", p.14–15). `µ′` is `diffLaw μ`; `sign(0) = +1`. -/
theorem claim_4_8 :
    ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → MemLp id 2 μ → 0 < variance id μ →
    ∀ (s : ℕ), 64 * halfVarRadius μ ^ 2 ≤ s →
    ∀ τ : ℝ, 8 ≤ τ →
      ENNReal.ofReal (1 / (16 * τ)) ≤
        gaussVec s {v | 1 / (16 * τ) ≤
          ∫ z, sineFn τ v z * sgn (signB (dot v z)) ∂(Measure.pi fun _ : Fin s => diffLaw μ)} := by sorry

end AgnHalfMem
