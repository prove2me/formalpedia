-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_claim_7_3
-- name    : CaiFourierSparse.Learning.claim_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:16:50.005544+00:00
-- url     : https://prove2.me/theorems/3712aa06-882f-4a49-abf1-794810b66b57
-- title:
--   Claim 7.3 — range of a cluster of Algorithm 2 in both regimes, and total range $\tilde O(k)d_{\min}=\tilde O(k^2/\varepsilon)$
-- statement:
--   Let $C\ge64$ be even, $k\ge1$ and $0<\varepsilon\le1/2$. For every output of Algorithm 2, a cluster with $\ell$ frequencies has range of length
--   $$r_\ell\le\begin{cases}d_{\min}\cdot O(\ell\log\ell),&\ell\le2\Delta_{k,\varepsilon}/d_{\min},\\ d_{\min}\cdot O(\ell)\cdot\log(2\Delta_{k,\varepsilon}/d_{\min}),&\ell>2\Delta_{k,\varepsilon}/d_{\min}.\end{cases}$$
--   Moreover $\sum_i|\operatorname{range}(C_i)|=\tilde O(k)\cdot d_{\min}=\tilde O(k^2/\varepsilon)$. The second regime is stated as printed.
--
--   Differences from the source:
--   - reading: C ≥ 64 an even integer (§6), C_M a universal constant with Δ_M = (C_M/2)(…) in (67) → every even C ≥ 64, with C_M = 4C² and C_H = 8C_M; reason: Claim 6.5(5) bounds the same radius Δ_M by 2C²(…), so C_M/2 = 2C²; quantifying over every admissible C is the strongest reading
--   - reading: log in the filter constants Δ_{ℓ,δ}, d_min and in the separation thresholds → base-2 logarithm; reason: the Fourier transform of (72) prints ⌈log₂ r⌉; the base of the filter's exponents must be fixed for the objects to be defined
--   - encoding: error ε (any) → 0 < ε ≤ 1/2; reason: the filter M_{k,ε} and Δ_{k,ε}, hence the clusters, are built under the section's standing assumption 0 < δ ≤ 1/2 (Claim 6.5, Lemma 6.1); it excludes only parameters for which these objects are not defined by the paper
--   - reading: x's clusters C₁, …, Cₙ from Algorithm 2 (the pair merged in each iteration is not specified) → every output of Algorithm 2 under every order of merges (IsAlg2Output); reason: the page fixes no tie-breaking; a statement about the algorithm's output must hold for each admissible run
--   - reading: Õ(g) (footnote 1) → A · g · log^e(2 + k/ε) with A > 0 and e ∈ ℕ fixed before all inputs; reason: the statement involves no bandlimit, so the polylog factor is taken in k/ε only (the stronger choice); 2 + k/ε keeps the factor positive at the smallest parameters
--   - encoding: O(ℓ log ℓ), O(ℓ) → A₁·ℓ·log ℓ and A₂·ℓ with A₁, A₂ > 0 fixed before k, ε, f and the clusters; reason: universal O-constants
--   - encoding: a cluster with ℓ frequencies → a cluster with ℓ labelled terms (|C|); reason: repeated frequencies are separate terms of x
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Claim 7.3, printed p. 35 (PDF p. 37)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Filter
import Definitions.Def_CaiFourierSparse_Learning_Clusters

namespace CaiFourierSparse.Learning

/-- Claim 7.3 (printed p. 35, PDF p. 37). Let `C ≥ 64` be an even integer. For every output
`C_1, …, C_n` of Algorithm 2 (any order of merges), a cluster with `ℓ` frequencies has range of
length `r_ℓ ≤ d_min · O(ℓ log ℓ)` if `ℓ ≤ 2Δ_{k,ε}/d_min`, and
`r_ℓ ≤ d_min · O(ℓ) · log(2Δ_{k,ε}/d_min)` if `ℓ > 2Δ_{k,ε}/d_min`. Moreover
`∑_i |range(C_i)| = Õ(k) · d_min = Õ(k²/ε)`, where `Õ(g)` is `A · g · log^e(2 + k/ε)`. -/
theorem claim_7_3 (C : ℕ) (hCe : Even C) (hC : 64 ≤ C) :
    ∃ (A₁ A₂ A₃ : ℝ) (e : ℕ), 0 < A₁ ∧ 0 < A₂ ∧ 0 < A₃ ∧
      ∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε → ε ≤ 1 / 2 →
        ∀ (f : Fin k → ℝ) (P : Finset (Finset (Fin k))), IsAlg2Output C ε f P →
          (∀ B ∈ P,
            ((B.card : ℝ) ≤ 2 * filterDelta C k ε / dMin C k ε →
              rangeLen f B ≤ dMin C k ε * (A₁ * B.card * Real.log B.card)) ∧
            (2 * filterDelta C k ε / dMin C k ε < B.card →
              rangeLen f B ≤
                dMin C k ε * (A₂ * B.card) * Real.log (2 * filterDelta C k ε / dMin C k ε))) ∧
          ∑ B ∈ P, rangeLen f B ≤ A₃ * k * Real.log (2 + k / ε) ^ e * dMin C k ε ∧
          ∑ B ∈ P, rangeLen f B ≤ A₃ * ((k : ℝ) ^ 2 / ε) * Real.log (2 + k / ε) ^ e := by sorry

end CaiFourierSparse.Learning
