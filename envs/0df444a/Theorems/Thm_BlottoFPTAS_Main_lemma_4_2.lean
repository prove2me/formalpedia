-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_4_2
-- name    : BlottoFPTAS.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:47.314546+00:00
-- url     : https://prove2.me/theorems/2c7ef66f-af77-49b4-b632-6d9c8c0b04f9
-- title:
--   Lemma 4.2 — an explicit mixture of at most seven uniform segment laws on {sum = B} with marginals Unif[0,a], Unif[0,d], (1 − p)δ₀ + p Unif[0,c], sampled in O(1) time
-- statement:
--   Let $B>0$, $0<a,d,c\le B$ and $0<p\le1$ with $a+d+pc=2B$. There is an explicit mixture of uniform distributions on at most seven line segments, with endpoints in $\{x\in\mathbb R^3:x\ge0,\ x_1+x_2+x_3=B\}$, whose marginals are $\mathrm{Unif}[0,a]$, $\mathrm{Unif}[0,d]$ and $(1-p)\delta_0+p\,\mathrm{Unif}[0,c]$; it can be sampled in $O(1)$ time. Appendix F.3 uses it with $p=1$ for equal budgets.
--
--   Differences from the source:
--   - reading: an explicit mixture … It can be sampled in O(1) time → there are a universal C₀ and one real-RAM program which, on input (B, a, d, c, p), samples exactly a mixture of at most seven segments with these properties and halts within C₀ steps on every tape; reason: explicitness is made precise as computability by a fixed program in constant time
--   - encoding: uniform distribution on a segment PQ → law of (1 − U)P + UQ with U ∼ Unif[0, 1] (segLaw); weights as a mixture; reason: the paper's own sampling description (p. 15)
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 15, Lemma 4.2

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Lotto
import Definitions.Def_BlottoFPTAS_Main_RealRAM

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 4.2** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 15).
There are a universal constant `C₀` and a real-RAM program such that, for all `B > 0`,
`0 < a, d, c ≤ B` and `0 < p ≤ 1` with `a + d + pc = 2B`, there are at most seven segments with
endpoints in `{x ∈ ℝ³ : x ≥ 0, x₀ + x₁ + x₂ = B}` and weights summing to one whose mixture of
uniform segment laws has marginals `Unif[0, a]`, `Unif[0, d]` and `(1 − p)δ₀ + p Unif[0, c]`, and
the program, run on the input `(B, a, d, c, p)`, samples exactly this mixture and halts within
`C₀` steps on every tape. -/
theorem lemma_4_2 :
    ∃ (C₀ : ℕ) (samp : RealRAM.Program), RealRAM.Admissible samp ∧
      ∀ B a d c p : ℝ, 0 < B → 0 < a → a ≤ B → 0 < d → d ≤ B → 0 < c → c ≤ B →
        0 < p → p ≤ 1 → a + d + p * c = 2 * B →
        ∃ (s : ℕ) (P Q : Fin s → Fin 3 → ℝ) (α : Fin s → ℝ),
          s ≤ 7 ∧ (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1 ∧
          (∀ i k, 0 ≤ P i k ∧ 0 ≤ Q i k) ∧ (∀ i, ∑ k, P i k = B ∧ ∑ k, Q i k = B) ∧
          marginal (segMixture α P Q) 0 = unifOn a ∧
          marginal (segMixture α P Q) 1 = unifOn d ∧
          marginal (segMixture α P Q) 2 = atomUnif p c ∧
          RealRAM.law samp [B, a, d, c, p] 3 = segMixture α P Q ∧
          ∀ ω : ℕ → ℝ, RealRAM.TapeInSupport ω →
            RealRAM.HaltsWithin samp [B, a, d, c, p] ω C₀ ∧
            ∃ out : List ℝ, RealRAM.output samp [B, a, d, c, p] ω = some out ∧
              out.length = 3 := by sorry

end BlottoFPTAS.Main
