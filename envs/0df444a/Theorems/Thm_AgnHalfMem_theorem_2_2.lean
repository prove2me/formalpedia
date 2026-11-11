-- Prove2me | Theorems.Thm_AgnHalfMem_theorem_2_2
-- name    : AgnHalfMem.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:11.560071+00:00
-- url     : https://prove2.me/theorems/db373847-fa6f-4163-878a-084d89735b1a
-- title:
--   Theorem 2.2 — extractor matrices: weak learning needs $ck'\ell'$ bits or $2^{r}$ samples
-- statement:
--   Let $\tfrac1{100}<c<\tfrac23$ and $\gamma>0$ with $\tfrac{3c}2<\gamma^2<1$. There are $K_0$ and $A>0$ such that the following holds. Let $H$ be a finite nonempty set, $\mu$ a probability measure on $X$, and $M:X\times H\to[-1,1]$ measurable in $x$ and a $(k',\ell')$-$L_2$-extractor with error $2^{-r'}$ for $\mu$, with $k',\ell',r'\ge K_0$. Let
--   $$
--   r=\min\Big\{\frac{r'}2,\ \frac{(1-\gamma)k'}2,\ \frac{(1-\gamma)\ell'-1}2\Big\}.
--   $$
--   Let $B$ be a randomized streaming algorithm (seed law $P$) that sees at most $2^r$ samples and has at most $2^{ck'\ell'}$ memory states, for the learning problem of $M$ under $\mu$. Then
--   $$
--   \Pr_{h,\omega,(x_t,y_t)}\Big[\mathrm{err}_h(\tilde h)\le \tfrac12-2^{-r/4}\Big]\ \le\ A\cdot 2^{-r/4},
--   $$
--   where $h$ is uniform on $H$, the samples are i.i.d. from $D_h$, and $\tilde h$ is the output.
--
--   This extends the memory–sample tradeoff of Garg–Raz–Tal [GRT18, Theorem 2] to infinite feature spaces and real-valued matrices; Theorem 3.1 applies it to agnostic learning.
--
--   Differences from the source:
--   - reading: "for sufficiently large k′, ℓ′ and r′", "at most O(2^{−r/4})" → ∃ K₀ A (after c, γ) with K₀ ≤ k′, ℓ′, r′ and bound A·2^{−r/4}; reason: standard meaning of the asymptotic statement
--   - reading: "error less than (1/2 − 2^{−r/4})" → error ≤ 1/2 − 2^{−r/4}; reason: Definition B.3's display uses ≤; the ≤-event contains the <-event, so this is the stronger reading
--   - reading: 3c/2 < γ² < 1 → 0 < γ; reason: γ scales the exponents of the proof
--   - generalization: "any streaming algorithm" (App. B: deterministic WLOG) → every jointly measurable seeded family of branching programs; probability over h, the seed and the samples (seededJointLaw); reason: deterministic algorithms are the case of a one-point seed space
--   - encoding: at most 2^r samples, at most ck′ℓ′ bits of memory; H a finite set → (T:ℝ) ≤ 2^r, card S ≤ 2^{c k′ ℓ′}; H finite nonempty with the discrete σ-algebra; M measurable in x; reason: Lean conventions; probabilities presuppose measurability
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 2.2, pp.7–8 (proof App. B, pp.28–41)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_StreamAlg
import Definitions.Def_AgnHalfMem_colLaw
import Definitions.Def_AgnHalfMem_AppBConstants

open MeasureTheory

universe u v w w'

namespace AgnHalfMem

/-- **Theorem 2.2 (extending [GRT18] to infinite-sized matrices).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Theorem 2.2, pp.7–8: "Let 1/100 < c < 2/3. Fix γ to be such that
3c/2 < γ² < 1. Let H be a finite set, and µ be a probability measure on X. Let M : X × H → [−1, 1]
be a matrix, which is a (k′, ℓ′)-L2-Extractor with error 2^{−r′}, for sufficiently large k′, ℓ′
and r′. Let r := min{r′/2, (1−γ)k′/2, ((1−γ)ℓ′ − 1)/2}. Let B be any streaming algorithm, that sees
at most 2^r samples and uses at most ck′ℓ′ bits of memory, for the learning problem that
corresponds to the matrix M w.r.t. probability measure µ. Then, the probability that the outputted
function achieves error less than (1/2 − 2^{−r/4}) on the data distribution is at most
O(2^{−r/4})."

**Formalization Note.** `r` is the statement's (p.8), not App. B's (p.29). "Sufficiently large"
is a threshold `K₀` and `O(·)` a constant `A`, both chosen after `c, γ`. The probability is over
`h` uniform, the seed and the samples (`seededJointLaw`); the event uses `≤` (Definition B.3's
display), which contains the "less than" event. Algorithms are randomized, jointly measurable
seeded programs (App. B fixes deterministic ones without loss of generality); `ck′ℓ′` bits is
`card S ≤ 2^{ck′ℓ′}`. `H` carries the discrete σ-algebra. -/
theorem theorem_2_2 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ A : ℝ, 0 < A ∧
      ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ r : ℝ, r = min (r' / 2) (min ((1 - γ) * k' / 2) (((1 - γ) * l' - 1) / 2)) →
      ∀ (Ω : Type w) (S : Type w') [MeasurableSpace Ω] [Fintype S] (T : ℕ)
        (B : StreamAlg Ω S X T) (P : Measure Ω), IsProbabilityMeasure P → IsMeasurableAlg B →
        (T : ℝ) ≤ (2 : ℝ) ^ r → (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (c * k' * l') →
        seededJointLaw μ M P T
            {q | errCol μ M q.1 ((B q.2.1).output q.2.2) ≤ 1 / 2 - (2 : ℝ) ^ (-(r / 4))} ≤
          ENNReal.ofReal (A * (2 : ℝ) ^ (-(r / 4))) := by sorry

end AgnHalfMem
