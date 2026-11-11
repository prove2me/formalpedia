-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_lemma_8_2
-- name    : CaiFourierSparse.Learning.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:17:00.77078+00:00
-- url     : https://prove2.me/theorems/1f28245a-cf0f-4b06-92ca-403511aaa1b2
-- title:
--   Lemma 8.2 — cluster energy is controlled by the spectral energy of any approximation on the bands
-- statement:
--   Let $C\ge64$ be even, $k\ge1$, $0<\varepsilon\le1/2$, and let $C_1,\dots,C_n$ be an output of Algorithm 2 for a $k$-Fourier-sparse $x$, with bands $I_i$ of (73). For every square-integrable approximate signal $w$ and every set $S$ of cluster indices,
--   $$\Big\|\sum_{i\in S}x_{C_i}\Big\|^2_{[-1,1]}\lesssim\int_{\bigcup_{i\in S}I_i}|\hat w(f)|^2\,df+\|x-w\|^2_{[-1,1]}+\|w\|^2_{\mathbb R\setminus[-1,1]}+\varepsilon\|x\|^2_{[-1,1]}\qquad\text{(eq. (81))}.$$
--
--   Differences from the source:
--   - reading: C ≥ 64 an even integer (§6), C_M a universal constant with Δ_M = (C_M/2)(…) in (67) → every even C ≥ 64, with C_M = 4C² and C_H = 8C_M; reason: Claim 6.5(5) bounds the same radius Δ_M by 2C²(…), so C_M/2 = 2C²; quantifying over every admissible C is the strongest reading
--   - reading: log in the filter constants Δ_{ℓ,δ}, d_min and in the separation thresholds → base-2 logarithm; reason: the Fourier transform of (72) prints ⌈log₂ r⌉; the base of the filter's exponents must be fixed for the objects to be defined
--   - encoding: error ε (any) → 0 < ε ≤ 1/2; reason: the filter M_{k,ε} and Δ_{k,ε}, hence the clusters, are built under the section's standing assumption 0 < δ ≤ 1/2 (Claim 6.5, Lemma 6.1); it excludes only parameters for which these objects are not defined by the paper
--   - reading: x's clusters C₁, …, Cₙ from Algorithm 2 (the pair merged in each iteration is not specified) → every output of Algorithm 2 under every order of merges (IsAlg2Output); reason: the page fixes no tie-breaking; a statement about the algorithm's output must hold for each admissible run
--   - encoding: any approximate signal w and ŵ → any w ∈ L²(ℝ), ŵ its Plancherel Fourier transform (l2ft); reason: the right-hand side needs ‖w‖_{ℝ∖[−1,1]} and ŵ; a non-L² w makes it infinite
--   - encoding: ≲ → ≤ A·(…) with A > 0 fixed before k, ε, x, the clusters, w and S; reason: the paper's ≲ hides a universal constant
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Lemma 8.2, printed p. 41 (PDF p. 43)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_Filter
import Definitions.Def_CaiFourierSparse_Learning_Clusters

namespace CaiFourierSparse.Learning

open MeasureTheory

/-- Lemma 8.2 (printed p. 41, PDF p. 43). Let `C ≥ 64` be an even integer. There is a constant
`A` such that for every `k ≥ 1`, `0 < ε ≤ 1/2`, every `k`-Fourier-sparse `x`, every output
`C_1, …, C_n` of Algorithm 2 with bands `I_i` of (73), every square-integrable approximate
signal `w : ℝ → ℂ` and every set `S` of clusters,
`‖∑_{i∈S} x_{C_i}‖²_{[-1,1]} ≤ A (∫_{⋃_{i∈S} I_i} |ŵ(f)|² df + ‖x - w‖²_{[-1,1]}
+ ‖w‖²_{ℝ \ [-1,1]} + ε ‖x‖²_{[-1,1]})` (eq. (81)). -/
theorem lemma_8_2 (C : ℕ) (hCe : Even C) (hC : 64 ≤ C) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε → ε ≤ 1 / 2 →
        ∀ (α : Fin k → ℂ) (f : Fin k → ℝ) (P : Finset (Finset (Fin k))), IsAlg2Output C ε f P →
          ∀ (w : ℝ → ℂ) (hw : MemLp w 2 volume), ∀ S ⊆ P,
            wsq (fun t => ∑ B ∈ S, subSignal α f B t) ≤
              ENNReal.ofReal A *
                ((∫⁻ ξ in ⋃ B ∈ S, band C ε f B, ‖l2ft hw ξ‖ₑ ^ 2) +
                  wsq (fun t => sparseSignal α f t - w t) + osq w +
                  ENNReal.ofReal ε * wsq (sparseSignal α f)) := by sorry

end CaiFourierSparse.Learning
