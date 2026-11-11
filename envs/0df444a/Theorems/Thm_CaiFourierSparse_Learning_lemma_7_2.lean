-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_lemma_7_2
-- name    : CaiFourierSparse.Learning.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:16:31.742877+00:00
-- url     : https://prove2.me/theorems/e8b4ba58-7d99-4a36-b189-61e44057e2a4
-- title:
--   Lemma 7.2 — near-additivity of energy over every subfamily of separated clusters, unfiltered and filtered
-- statement:
--   Let $C\ge64$ be even, $k\ge1$, $0<\varepsilon\le1/2$, $d_{\min}=C_Hk\log^{1.5}(k/\varepsilon)/\varepsilon$, and let $C_1,\dots,C_n$ partition the terms of a $k$-Fourier-sparse $x$ into clusters with $\operatorname{dist}(C_i,C_j)\ge\min\{d_{\min}\min\{|C_i|,|C_j|\},2\Delta_{k,\varepsilon}\}$ for all $i\ne j$. Then for every $S\subseteq\{1,\dots,n\}$,
--   $$\Big\|\sum_{i\in S}x_{C_i}\Big\|^2_{[-1,1]}=(1\pm O(\varepsilon))\sum_{i\in S}\|x_{C_i}\|^2_{[-1,1]},\qquad\Big\|M_{k,\varepsilon}\sum_{i\in S}x_{C_i}\Big\|^2_2=(1\pm O(\varepsilon))\sum_{i\in S}\|M_{k,\varepsilon}x_{C_i}\|_2^2,$$
--   and in particular $\|x\|^2_{[-1,1]}=(1\pm O(\varepsilon))\sum_i\|x_{C_i}\|^2_{[-1,1]}=(1\pm O(\varepsilon))\sum_i\|M_{k,\varepsilon}x_{C_i}\|_2^2$.
--
--   Differences from the source:
--   - reading: C ≥ 64 an even integer (§6), C_M a universal constant with Δ_M = (C_M/2)(…) in (67) → every even C ≥ 64, with C_M = 4C² and C_H = 8C_M; reason: Claim 6.5(5) bounds the same radius Δ_M by 2C²(…), so C_M/2 = 2C²; quantifying over every admissible C is the strongest reading
--   - reading: log in the filter constants Δ_{ℓ,δ}, d_min and in the separation thresholds → base-2 logarithm; reason: the Fourier transform of (72) prints ⌈log₂ r⌉; the base of the filter's exponents must be fixed for the objects to be defined
--   - encoding: error ε (any) → 0 < ε ≤ 1/2; reason: the filter M_{k,ε} and Δ_{k,ε}, hence the clusters, are built under the section's standing assumption 0 < δ ≤ 1/2 (Claim 6.5, Lemma 6.1); it excludes only parameters for which these objects are not defined by the paper
--   - encoding: n clusters C₁, …, Cₙ of x (with the 'in particular' identity for x) → a partition of the k labelled terms into nonempty disjoint clusters (IsClusterPartition); reason: the identity ‖x‖² = (1 ± O(ε))Σ‖x_{C_i}‖² requires the clusters to partition x
--   - encoding: a = (1 ± O(ε))·b → ApproxEq (A·ε): (1 − Aε)b ≤ a ≤ (1 + Aε)b with A fixed before k, ε, x and the clusters; reason: definition of the ± notation (§2)
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Lemma 7.2, printed p. 35 (PDF p. 37)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_Filter
import Definitions.Def_CaiFourierSparse_Learning_Clusters

namespace CaiFourierSparse.Learning

/-- Lemma 7.2 (printed p. 35, PDF p. 37). Let `C ≥ 64` be an even integer. There is a constant
`A` such that for every `k ≥ 1`, `0 < ε ≤ 1/2`, every `k`-Fourier-sparse `x` and every partition
of its `k` terms into clusters `C_1, …, C_n` with
`dist(C_i, C_j) ≥ min{d_min · min{|C_i|, |C_j|}, 2Δ_{k,ε}}` for all `i ≠ j`
(`d_min = C_H k log^{1.5}(k/ε)/ε`), every subfamily `S` satisfies
`‖∑_{i∈S} x_{C_i}‖²_{[-1,1]} = (1 ± Aε) ∑_{i∈S} ‖x_{C_i}‖²_{[-1,1]}` and
`‖M_{k,ε} ∑_{i∈S} x_{C_i}‖²₂ = (1 ± Aε) ∑_{i∈S} ‖M_{k,ε} x_{C_i}‖²₂`; in particular
`‖x‖²_{[-1,1]} = (1 ± Aε) ∑_i ‖x_{C_i}‖²_{[-1,1]} = (1 ± Aε) ∑_i ‖M_{k,ε} x_{C_i}‖²₂`. -/
theorem lemma_7_2 (C : ℕ) (hCe : Even C) (hC : 64 ≤ C) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε → ε ≤ 1 / 2 →
        ∀ (α : Fin k → ℂ) (f : Fin k → ℝ) (P : Finset (Finset (Fin k))),
          IsClusterPartition P →
          (∀ A₁ ∈ P, ∀ A₂ ∈ P, A₁ ≠ A₂ →
            min (dMin C k ε * (min A₁.card A₂.card : ℕ)) (2 * filterDelta C k ε) ≤
              clusterDist f A₁ A₂) →
          (∀ S ⊆ P,
            ApproxEq (A * ε) (wsq (fun t => ∑ B ∈ S, subSignal α f B t))
              (∑ B ∈ S, wsq (subSignal α f B)) ∧
            ApproxEq (A * ε) (lsq (filtered C k k ε (fun t => ∑ B ∈ S, subSignal α f B t)))
              (∑ B ∈ S, lsq (filtered C k k ε (subSignal α f B)))) ∧
          ApproxEq (A * ε) (wsq (sparseSignal α f)) (∑ B ∈ P, wsq (subSignal α f B)) ∧
          ApproxEq (A * ε) (wsq (sparseSignal α f))
            (∑ B ∈ P, lsq (filtered C k k ε (subSignal α f B))) := by sorry

end CaiFourierSparse.Learning
