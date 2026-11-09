-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_claim_4_5
-- name    : BLTCounting.AccuracySpace.claim_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:19.45743+00:00
-- url     : https://prove2.me/theorems/1beea015-203e-444f-b160-3b4e0ea04071
-- title:
--   Entrywise Toeplitz approximation
-- statement:
--   Let $R\ge1$ be an integer, let $0<h\le1$ with $Rh>1$, let $Q$ be the matrix of equation (33) for $K$ blocks, and let $F(f)=Q^*\widehat H_S(f)Q$. There is an absolute constant $c>0$ with
--   $$\bigl|F(f)[i,j]-h\,c_0((i-j)h)\bigr|\le c\Bigl(h+\frac1{Rh}+\frac1R\Bigr)h\,c_0((i-j)h)$$
--   simultaneously for all $0\le i,j<K$. The compressed matrix is entrywise close to the Toeplitz matrix $V_h$, in a relative sense.
--
--   Differences from the source:
--   - generalization: the parameters of equation (28) with $K=\lfloor\ell/h\rfloor$ → all integers $R\ge1$, all $0<h\le1$ with $Rh>1$ and all $K$; reason: the bound depends only on these ranges, which the source verifies for its parameters; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 4.5, printed p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

namespace BLTCounting.AccuracySpace

/-- Claim 4.5, PDF p. 29: for the matrix `Q` of equation (33) and `F(f) = Q* Ĥ_S(f) Q`, there is an
absolute constant `c > 0` with
`|F(f)[i, j] - h c₀((i-j)h)| ≤ c (h + 1/(Rh) + 1/R) h c₀((i-j)h)` for all `i`, `j`, in the regime
`0 < h ≤ 1`, `Rh > 1` in which the construction is made. -/
theorem claim_4_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ (R : ℕ) (h : ℝ) (K : ℕ), 1 ≤ R → 0 < h → h ≤ 1 → 1 < (R : ℝ) * h →
      ∀ i j : Fin K,
        ‖blockCompression R h K sqrtSeq i j -
            ((h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) : ℝ) : ℂ)‖ ≤
          c * (h + 1 / ((R : ℝ) * h) + 1 / (R : ℝ)) *
            (h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h)) := by sorry

end BLTCounting.AccuracySpace
