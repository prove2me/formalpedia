-- Prove2me | Theorems.Thm_AgnHalfMem_claim_B_13
-- name    : AgnHalfMem.claim_B_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:48.9+00:00
-- url     : https://prove2.me/theorems/fb448819-6425-4eed-92bc-d968ba02bcb5
-- title:
--   Claim B.13 — one-step progress towards a target vertex is slow
-- statement:
--   In the setting of Appendix B (see Lemma B.4), let $s$ be a target vertex and $v$ a vertex of $B$ with $\Pr(v)>0$, and let $\Gamma_{\mathrm{out}}(v)$ be the edges leaving $v$ with positive probability. Then
--   $$
--   \sum_{e\in\Gamma_{\mathrm{out}}(v)}\frac{\Pr(e)}{\Pr(v)}\,\langle P_{h|e},P_{h|s}\rangle^{k}\ \le\ \langle P_{h|v},P_{h|s}\rangle^{k}\,(1+2^{-r})^{k}+(2^{-2n+2})^{k},
--   $$
--   with $k=\gamma k'$, $n=\log_2|H|$ and the uniform-normalized inner product.
--
--   Differences from the source:
--   - encoding: standing assumptions of App. B stated once (p.29: 1/100 < c < 2/3, 3c/2 < γ² < 1, M a (k′,ℓ′)-extractor with error 2^{−r′} "for sufficiently large k′, ℓ′ and r′", B a branching program) → hypotheses AppBConstants c γ; ∃ K₀ (after c, γ) with K₀ ≤ k′, ℓ′, r′; M measurable in x with values in [−1,1] and IsL2Extractor μ M k′ ℓ′ r′; B a measurable deterministic BP on a finite state type S; reason: the section's standing assumptions are hypotheses of every claim; measurability is what makes the probabilities defined
--   - reading: γ with 3c/2 < γ² < 1; "k := γk" → 0 < γ; k = γk′ (appBk); reason: γ scales the exponents k, ℓ; the typo is corrected by p.37 "Recall that k = γk′"
--   - encoding: vertices of layers with at most 2^{ck′ℓ′} vertices, edges with labels A_e, P_{h|v} for Pr(v) > 0 → vertices (i, v) with v in one finite type S; edges (v, u) with A_e = {z | step i v z = u}; P_{h|v} := 0 when Pr(v) = 0; reason: Lean conventions for the layered graph; the zero posterior only arises on null vertices
--   - generalization: s a fixed significant vertex (p.33) → s any vertex of any layer; reason: the proof uses only Claim B.10 for s, and P_{h|s} = 0 when Pr(s) = 0 makes both sides trivial
--   - encoding: sum over Γ_out(v) (edges with Pr(e) > 0) → sum over all u : S; reason: edges of probability 0 contribute 0
--   - generalization: B of length m = 2^r and width at most 2^{ck′ℓ′} (p.30, “We assume B is a branching program with length m = 2^r and width at most 2^{ck′ℓ′}”) → any length T and any finite state type S, with no length or width bound; reason: the proof works at one vertex or edge and uses neither bound; programs of length 2^r and width at most 2^{ck′ℓ′} are instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.13, p.37 (proof pp.37–39)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AppBConstants
import Definitions.Def_AgnHalfMem_truncAlive

open MeasureTheory

universe u v w

namespace AgnHalfMem

/-- **Claim B.13 (one-step progress).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.13, p.37: "For every vertex v of B,
such that Pr(v) > 0, Σ_{e∈Γ_out} (Pr(e)/Pr(v)) · ⟨P_{h|e}, P_{h|s}⟩^k ≤
⟨P_{h|v}, P_{h|s}⟩^k · (1 + 2^{−r})^k + (2^{−2n+2})^k".

**Formalization Note.** The standing assumptions of App. B (p.29) are hypotheses: `c, γ` with
`AppBConstants c γ`; `M : X × H → [−1, 1]` measurable in `x`, a `(k′, ℓ′)`-L2-extractor with error
`2^{−r′}` for `k′, ℓ′, r′ ≥ K₀` ("sufficiently large", `K₀` chosen after `c, γ`); `ℓ = γℓ′/3`
(`appBl`), `r` as on p.29 (`appBr`), `k = γk′` (`appBk`); `B` a deterministic, measurable
program of length `T` on the states `S`. Vertices are pairs (layer `i`, state `v`); all
probabilities are under the joint law (`h` uniform, samples i.i.d. from `D_h`); `P_{h|v} = 0` when
`Pr(v) = 0`. The target `s` (layer `j`) is any vertex (in the paper a fixed significant vertex; the proof
uses only Claim B.10 for `s`, and `P_{h|s} = 0` when `Pr(s) = 0`). `Γ_out(v)` is the set of
out-edges `(v, u)` with `Pr(e) > 0`; the sum over all `u` adds only zero terms. `⟨·,·⟩` is
uniform-normalized and `(·)^k` is the real power, `k = γk′`. -/
theorem claim_B_13 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ : ℝ,
    ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ (S : Type w) [Fintype S] (T : ℕ) (B : BP S X T), B.IsMeasurableBP →
      ∀ (j : ℕ) (s : S) (i : ℕ) (v : S), 0 < vertexProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v →
        ∑ u, edgeProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v u / vertexProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v *
            (ip (edgePost μ M B (appBl γ l') (appBr γ k' l' r') r' i v u) (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' j s)) ^ appBk γ k' ≤
          (ip (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' j s)) ^ appBk γ k' *
              (1 + (2 : ℝ) ^ (-appBr γ k' l' r')) ^ appBk γ k' +
            ((2 : ℝ) ^ (-2 * logCard H + 2)) ^ appBk γ k' := by sorry

end AgnHalfMem
