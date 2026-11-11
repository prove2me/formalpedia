-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_fact_2_2
-- name    : EntAssistOneWay.Separation.fact_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:11.239351+00:00
-- url     : https://prove2.me/theorems/ba046fc5-e70a-43a1-9fc0-601e84a8af73
-- title:
--   Fact 2.2 — complex Hermitian Rademacher trace moments
-- statement:
--   Let $A_1,\ldots,A_n$ be fixed Hermitian $d\times d$ complex matrices and let the $c_i$ be independent uniform signs. For every even integer $p\ge2$,
--   $$\mathbb E_c\operatorname{tr}\!\left(\Bigl(\sum_i c_iA_i\Bigr)^p\right)\le d\left(\prod_{j=1}^{p/2}(2j-1)\right)\left\|\sum_i A_i^2\right\|_\infty^{p/2}.$$
--   This cited result of Tropp is the moment bound used for the independent-matrix corollary. The matrices are complex Hermitian, including the cases not covered by the catalog's real-symmetric moment results.
--
--   Differences from the source:
--   - encoding: independent uniform signs and a real trace → uniform averaging over Boolean sign vectors and the real part of the trace; reason: Boolean vectors label all sign choices; the even power of a Hermitian matrix has real trace
--   - encoding: the product over j = 1,…,p/2 → the product of 2j+1 over j = 0,…,p/2−1; reason: zero-based finite indexing gives the identical factors
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 11, Fact 2.2 ([Tro16, Eq. (4.9)])

import Definitions.Def_EntAssistOneWay_Separation_Analysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Fact 2.2, p. 11; the complex Hermitian version. -/
theorem fact_2_2 (n d : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (p : ℕ) (hp : Even p) (hp₂ : 2 ≤ p) :
    uniformAverage (fun c : Fin n → Bool =>
      ((∑ i, (if c i then (1 : ℂ) else -1) • A i) ^ p).trace.re) ≤
      (d : ℝ) * (∏ j ∈ Finset.range (p / 2), (2 * (j : ℝ) + 1)) *
        spectralNorm (∑ i, A i ^ 2) ^ (p / 2) := by sorry

end

end EntAssistOneWay.Separation
