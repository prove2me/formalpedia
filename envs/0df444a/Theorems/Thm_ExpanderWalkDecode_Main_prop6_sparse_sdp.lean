-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_prop6_sparse_sdp
-- name    : ExpanderWalkDecode.Main.prop6_sparse_sdp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:25.050004+00:00
-- url     : https://prove2.me/theorems/3d539537-d9c2-4599-ae01-e3ab17f0f2a3
-- title:
--   Proposition 6 ([JST21], Lemma 4.17) (corrected: regularized logarithm in $\Delta$) — sparse SDP approximation with Gram vectors
-- statement:
--   There are absolute constants $C>0$, $K$, $c$, $p$ and one randomized program with the following property. Let $k,m\in\mathbb N$, $0<\theta\le1/2$, $0<\delta<1/2$, and let $A\in\mathbb R^{k\times k}$ be symmetric with at most $m$ nonzero entries, supplied as the list of its nonzero entries (in any order). Set
--   $$\Delta=\big\lceil C\theta^{-2}\log\max(2,k)\big\rceil .$$
--   Run on this input, the program halts within $K(m+k+1)(\log_2(m+k+2))^p\,\theta^{-c}\log(1/\delta)=\tilde O(m+k)\cdot\mathrm{poly}(1/\theta)\cdot\log(1/\delta)$ steps, always outputs $\Delta$-dimensional Gram vectors of a matrix $Q\in\mathcal E$ (positive semidefinite with diagonal at most $1$), and with probability at least $1-\delta$
--   $$A\bullet Q\ge\max_{V\in\mathcal E}A\bullet V-\theta\sum_{i,j=1}^k|A_{i,j}| .$$
--
--   It is the engine of the fast gradient step (Claim 7).
--
--   Differences from the source:
--   - correction: Δ := ⌈Cθ^{-2} log k⌉ → Δ := ⌈Cθ^{-2} log max(2, k)⌉; reason: the printed statement is false at k = m = 1, θ = 1/2, δ = 1/4, A = [1]: Δ = 0, so Q = [0] and A•Q = 0, while max_V A•V − θΣ|A_ij| = 1 − 1/2 = 1/2
--   - reading: outputs Δ-dimensional Gram vectors of Q ∈ E such that with probability ≥ 1−δ, A•Q ≥ … → Q ∈ E on every run; the inequality with probability ≥ 1−δ; reason: the stronger of the two readings
--   - reading: time Õ(m+k)·poly(1/θ)·log(1/δ), A supplied by its nonzero entries → K(m+k+1)(log₂(m+k+2))^p θ^{-c} log(1/δ) with absolute constants on the machine of this mission; the nonzero entries listed once each in any order; reason: unfolding of the asymptotic notation and of the input format
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 28 (PDF p. 31), Appendix C.1, Proposition 6

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Proposition 6 ([JST21], Lemma 4.17) (Appendix C.1, p. 28), with the dimension
`Δ = ⌈C θ⁻² log(max(2, k))⌉` (corrected from `log k`): one randomized program, given a symmetric
`k × k` matrix `A` with at most `m` nonzero entries (supplied by its nonzero entries), and
`0 < θ ≤ 1/2`, `0 < δ < 1/2`, runs in time `K (m + k + 1)(log₂(m+k+2))^p θ^{-c} log(1/δ)` and always
outputs `Δ`-dimensional Gram vectors of a matrix `Q ∈ E`; with probability at least `1 - δ`,
`A • Q ≥ max_{V ∈ E} A • V - θ ∑_{i,j} |A_{ij}|`. -/
theorem prop6_sparse_sdp :
    ∃ (C K c : ℝ) (p : ℕ) (P : Program), 0 < C ∧ Admissible P ∧
      ∀ (k m : ℕ) (θ δ : ℝ) (A : Matrix (Fin k) (Fin k) ℝ) (entries : List (Fin k × Fin k)),
        0 < θ → θ ≤ 1 / 2 → 0 < δ → δ < 1 / 2 → Aᵀ = A → entries.length ≤ m → entries.Nodup →
        (∀ i j, (i, j) ∈ entries ↔ A i j ≠ 0) →
        ∃ T : ℕ,
          (T : ℝ) ≤ K * ((m : ℝ) + k + 1) * Real.logb 2 ((m : ℝ) + k + 2) ^ p * (1 / θ) ^ c
            * Real.log (1 / δ) ∧
          HaltsWithin P (sparseInput k m θ δ A entries) T ∧
          (∀ bits : Fin T → Bool,
            (run P (extendBits bits) (sparseInput k m θ δ A entries) T).output.length
              = k * ⌈C * θ ^ (-2 : ℤ) * Real.log (max 2 (k : ℝ))⌉₊ ∧
            gramOf (rowsOf k ⌈C * θ ^ (-2 : ℤ) * Real.log (max 2 (k : ℝ))⌉₊
              (run P (extendBits bits) (sparseInput k m θ δ A entries) T).output) ∈ EllK k) ∧
          1 - δ ≤ successProb P (sparseInput k m θ δ A entries) T (fun out =>
            ∀ V ∈ EllK k, (∑ i, ∑ j, A i j * V i j) - θ * ∑ i, ∑ j, |A i j| ≤
              ∑ i, ∑ j, A i j *
                gramOf (rowsOf k ⌈C * θ ^ (-2 : ℤ) * Real.log (max 2 (k : ℝ))⌉₊ out) i j) := by sorry

end ExpanderWalkDecode.Main
