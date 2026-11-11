-- Prove2me | Theorems.Thm_AgnHalfMem_lemma_B_4
-- name    : AgnHalfMem.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:27.767137+00:00
-- url     : https://prove2.me/theorems/1b493ba2-4f78-46d4-b0ce-9a7de9a366d6
-- title:
--   Lemma B.4 — the truncated path reaches a significant vertex with probability $O(2^{-r})$
-- statement:
--   Assume the setting of Appendix B: $c,\gamma$ as in Theorem 2.2, $M:X\times H\to[-1,1]$ measurable in $x$ and a $(k',\ell')$-$L_2$-extractor with error $2^{-r'}$ for $\mu$, with $k',\ell',r'\ge K_0$, and $k=\gamma k'$, $\ell=\gamma\ell'/3$, $r=\min\{r'/2,(1-\gamma)k'/2,(1-\gamma)\ell'/2-1\}$. Let $B$ be a measurable deterministic branching program of length $T\le 2^r$ and width at most $2^{ck'\ell'}$. Then
--   $$
--   \Pr\big[\mathcal T\text{ reaches a significant vertex}\big]\ \le\ A\cdot 2^{-r},
--   $$
--   where $\mathcal T$ is the truncated path and $K_0,A$ depend only on $c,\gamma$.
--
--   This is the main technical lemma of the proof of Theorem 2.2: it shows that a memory-bounded program rarely accumulates non-negligible information about $h$.
--
--   Differences from the source:
--   - encoding: standing assumptions of App. B stated once (p.29: 1/100 < c < 2/3, 3c/2 < γ² < 1, M a (k′,ℓ′)-extractor with error 2^{−r′} "for sufficiently large k′, ℓ′ and r′", B a branching program) → hypotheses AppBConstants c γ; ∃ K₀ (after c, γ) with K₀ ≤ k′, ℓ′, r′; M measurable in x with values in [−1,1] and IsL2Extractor μ M k′ ℓ′ r′; B a measurable deterministic BP on a finite state type S; reason: the section's standing assumptions are hypotheses of every claim; measurability is what makes the probabilities defined
--   - reading: γ with 3c/2 < γ² < 1; "k := γk" → 0 < γ; k = γk′ (appBk); reason: γ scales the exponents k, ℓ; the typo is corrected by p.37 "Recall that k = γk′"
--   - encoding: vertices of layers with at most 2^{ck′ℓ′} vertices, edges with labels A_e, P_{h|v} for Pr(v) > 0 → vertices (i, v) with v in one finite type S; edges (v, u) with A_e = {z | step i v z = u}; P_{h|v} := 0 when Pr(v) = 0; reason: Lean conventions for the layered graph; the zero posterior only arises on null vertices
--   - reading: O(2^{−r}) → A·2^{−r} with A chosen after c, γ; reason: standard meaning of O
--   - generalization: B of length m = 2^r (p.30) → any length T with T ≤ 2^r; reason: a shorter program is covered; the union bound only needs at most 2^r layers
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Lemma B.4, p.30 (proof pp.33–41)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AppBConstants
import Definitions.Def_AgnHalfMem_truncAlive

open MeasureTheory

universe u v w

namespace AgnHalfMem

/-- **Lemma B.4 (the truncated path rarely reaches a significant vertex).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Lemma B.4,
p.30: "The probability that T reaches a significant vertex is at most O(2^{−r})".

**Formalization Note.** The standing assumptions of App. B (p.29) are hypotheses: `c, γ` with
`AppBConstants c γ`; `M : X × H → [−1, 1]` measurable in `x`, a `(k′, ℓ′)`-L2-extractor with error
`2^{−r′}` for `k′, ℓ′, r′ ≥ K₀` ("sufficiently large", `K₀` chosen after `c, γ`); `ℓ = γℓ′/3`
(`appBl`), `r` as on p.29 (`appBr`), `k = γk′` (`appBk`); `B` a deterministic, measurable
program of length `T` on the states `S`. Vertices are pairs (layer `i`, state `v`); all
probabilities are under the joint law (`h` uniform, samples i.i.d. from `D_h`); `P_{h|v} = 0` when
`Pr(v) = 0`. Lemma B.4 is proved for B of length m = 2^r and width at most 2^{ck′ℓ′} (p.30); here
the length is any `T ≤ 2^r` and the width `card S ≤ 2^{ck′ℓ′}`. `O(·)` is a constant `A`. -/
theorem lemma_B_4 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ A : ℝ, 0 < A ∧
    ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ (S : Type w) [Fintype S] (T : ℕ) (B : BP S X T), B.IsMeasurableBP →
      (T : ℝ) ≤ (2 : ℝ) ^ appBr γ k' l' r' → (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (c * k' * l') →
      jointLaw μ M T (⋃ (i : ℕ) (v : S)
          (_ : IsSignificant (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (appBl γ l')),
          truncAlive μ M B (appBl γ l') (appBr γ k' l' r') r' i v) ≤
        ENNReal.ofReal (A * (2 : ℝ) ^ (-appBr γ k' l' r')) := by sorry

end AgnHalfMem
