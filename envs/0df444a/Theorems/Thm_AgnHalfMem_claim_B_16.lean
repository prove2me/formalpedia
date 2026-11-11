-- Prove2me | Theorems.Thm_AgnHalfMem_claim_B_16
-- name    : AgnHalfMem.claim_B_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:53.644443+00:00
-- url     : https://prove2.me/theorems/7b1c5ea4-c1a7-476b-a17d-3e1527e8576d
-- title:
--   Claim B.16 — total progress $Z_i\le 2^{4k+2r}\cdot2^{-2kn}$
-- statement:
--   In the setting of Appendix B (see Lemma B.4), let $B$ have length $T\le2^r$ and let $s$ be a target vertex. For every $i\in\{1,\dots,T\}$,
--   $$
--   Z_i=\sum_{v\in L_i}\Pr(v)\,\langle P_{h|v},P_{h|s}\rangle^{k}\ \le\ 2^{4k+2r}\cdot 2^{-2k\cdot n}.
--   $$
--   Compared with $Z_i\ge \Pr(s)\,2^{2\ell k}2^{-2kn}$ for a significant $s$ in layer $i$, this yields $\Pr(s)\le 2^{-\Omega(k'\ell')}$ and hence Lemma B.4.
--
--   Differences from the source:
--   - encoding: standing assumptions of App. B stated once (p.29: 1/100 < c < 2/3, 3c/2 < γ² < 1, M a (k′,ℓ′)-extractor with error 2^{−r′} "for sufficiently large k′, ℓ′ and r′", B a branching program) → hypotheses AppBConstants c γ; ∃ K₀ (after c, γ) with K₀ ≤ k′, ℓ′, r′; M measurable in x with values in [−1,1] and IsL2Extractor μ M k′ ℓ′ r′; B a measurable deterministic BP on a finite state type S; reason: the section's standing assumptions are hypotheses of every claim; measurability is what makes the probabilities defined
--   - reading: γ with 3c/2 < γ² < 1; "k := γk" → 0 < γ; k = γk′ (appBk); reason: γ scales the exponents k, ℓ; the typo is corrected by p.37 "Recall that k = γk′"
--   - encoding: vertices of layers with at most 2^{ck′ℓ′} vertices, edges with labels A_e, P_{h|v} for Pr(v) > 0 → vertices (i, v) with v in one finite type S; edges (v, u) with A_e = {z | step i v z = u}; P_{h|v} := 0 when Pr(v) = 0; reason: Lean conventions for the layered graph; the zero posterior only arises on null vertices
--   - generalization: s a fixed significant vertex; B of length m = 2^r → s any vertex; any length T ≤ 2^r; reason: the proof uses only Claim B.13 (valid for any s) and i ≤ m ≤ 2^r
--   - generalization: B of width at most 2^{ck′ℓ′} (p.30) → any finite state type S, with no width bound; reason: the proof (Claims B.13–B.15 and the induction on i) never uses the width; programs of width at most 2^{ck′ℓ′} are instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.16, p.40 (proof pp.40–41)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AppBConstants
import Definitions.Def_AgnHalfMem_truncAlive

open MeasureTheory

universe u v w

namespace AgnHalfMem

/-- **Claim B.16 (total progress).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.16, p.40: "For every i ∈ {1, …, m},
Z_i ≤ 2^{4k+2r} · 2^{−2k·n}."

**Formalization Note.** The standing assumptions of App. B (p.29) are hypotheses: `c, γ` with
`AppBConstants c γ`; `M : X × H → [−1, 1]` measurable in `x`, a `(k′, ℓ′)`-L2-extractor with error
`2^{−r′}` for `k′, ℓ′, r′ ≥ K₀` ("sufficiently large", `K₀` chosen after `c, γ`); `ℓ = γℓ′/3`
(`appBl`), `r` as on p.29 (`appBr`), `k = γk′` (`appBk`); `B` a deterministic, measurable
program of length `T` on the states `S`. Vertices are pairs (layer `i`, state `v`); all
probabilities are under the joint law (`h` uniform, samples i.i.d. from `D_h`); `P_{h|v} = 0` when
`Pr(v) = 0`. `Z_i = Σ_{v∈L_i} Pr(v)⟨P_{h|v}, P_{h|s}⟩^k` (`progressZ`, p.37) for any target vertex `s` of
layer `j` (the paper's fixed significant `s`; see Claim B.13). The length `m = 2^r` of the
paper is generalized to any `T ≤ 2^r`. -/
theorem claim_B_16 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ : ℝ,
    ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ (S : Type w) [Fintype S] (T : ℕ) (B : BP S X T), B.IsMeasurableBP →
      (T : ℝ) ≤ (2 : ℝ) ^ appBr γ k' l' r' →
      ∀ (j : ℕ) (s : S) (i : ℕ), 1 ≤ i → i ≤ T →
        progressZ μ M B (appBl γ l') (appBr γ k' l' r') r' (appBk γ k') i j s ≤
          (2 : ℝ) ^ (4 * appBk γ k' + 2 * appBr γ k' l' r') *
            (2 : ℝ) ^ (-(2 * appBk γ k' * logCard H)) := by sorry

end AgnHalfMem
