-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_8_1
-- name    : AlgCoverage.OddOrder.eq_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:47:16.248458+00:00
-- url     : https://prove2.me/theorems/9df0d1e6-f18f-4385-821a-eddd62900edf
-- title:
--   §8.1, Eq. (8.1) — broken-circuit bracketing $\Pr(H=\varnothing)\le\sum_{i\le r}(-1)^ia_i+\mathbb ED_r$ ($r$ even), reversed for $r$ odd
-- statement:
--   Let $G$ be a finite group of odd order with a supplied series (6.1), $B\subseteq G\setminus\{1_G\}$ a deterministic target set, and $X\in G^k$ iid uniform inputs. With the event universe $E=(\{0,1\}^k\setminus\{0\})\times B$ under a fixed total order, the active set $H$, the family $K$, the coefficients $a_i$ and the defect count $D_r$ of §8, for every cutoff $r$:
--   $$\Pr(H=\varnothing)\le\sum_{i=0}^r(-1)^ia_i+\mathbb ED_r\quad(r\text{ even}),\qquad \Pr(H=\varnothing)\ge\sum_{i=0}^r(-1)^ia_i-\mathbb ED_r\quad(r\text{ odd}). \tag{8.1}$$
--   This is the truncated, family-restricted inclusion–exclusion with an explicit defect term on which the relative-error bound (Proposition 8.1) rests.
--
--   Differences from the source:
--   - encoding: a supplied G-normal elementary-abelian series (6.1) and FULL as surjectivity of the coefficient map at every layer → s : NormalEASeries G (0-based layers A (r+1)/A r, every layer nontrivial: d_r ≥ 1) and FULL s x U: every target in A_{r+1}^j is hit modulo A_r by the layer word ∏ P_i a_i P_i⁻¹ for some lifts a ∈ A_{r+1}^k; reason: the layer quotient is abelian and normal in G/A_r, so this is surjectivity of the induced linear coefficient map with coefficients θ(prefix) of form (5.1); d_r ≥ 1 is the reading of (6.1) declared in eq_6_1 (J ≤ log₃ N needs it), and a series with trivial layers collapses to one without them with the same FULL and no larger J
--   - encoding: a fixed total order on E → a rank ord : (Fin k → Bool) × G → ℕ injective on E; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a := min H, |I| ≤ r − 1, and a₀ = 1 → an a ∈ H of minimal rank, |I| + 1 ≤ r, and coeffA … 0 = 1; reason: the same conditions without natural-number subtraction or a choice of minimum
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 24 (PDF 25), §8.1, Eq. (8.1)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Series
import Definitions.Def_AlgCoverage_OddOrder_Sieve

namespace AlgCoverage.OddOrder

/-- §8.1, Eq. (8.1) (broken-circuit bracketing), Lin, printed p. 24 / PDF 25. `G` of odd order with a
supplied series, a nonidentity target set `B`, `k` iid inputs, the event universe
`E = ({0,1}^k \ {0}) × B` with a fixed total order (`ord` injective on `E`), active set `H`, family `K`,
coefficients `a_i` and defect count `D_r`. For even `r`:
`Pr(H = ∅) ≤ ∑_{i=0}^r (−1)^i a_i + E D_r`; for odd `r`: `Pr(H = ∅) ≥ ∑_{i=0}^r (−1)^i a_i − E D_r`. -/
theorem eq_8_1 (G : Type*) [Group G] [Fintype G] (hodd : Odd (Fintype.card G))
    (s : NormalEASeries G) (k : ℕ) (B : Finset G) (hB : (1 : G) ∉ B)
    (ord : (Fin k → Bool) × G → ℕ) (hord : Set.InjOn ord (eventSet k B : Set ((Fin k → Bool) × G)))
    (r : ℕ) :
    (Even r →
      probIid G k (fun x => activeSet B x = ∅) ≤
        ∑ i ∈ Finset.range (r + 1), (-1 : ℝ) ^ i * coeffA s k B ord i +
          expIid G k (fun x => (defectCount s B ord r x : ℝ))) ∧
    (Odd r →
      ∑ i ∈ Finset.range (r + 1), (-1 : ℝ) ^ i * coeffA s k B ord i -
          expIid G k (fun x => (defectCount s B ord r x : ℝ)) ≤
        probIid G k (fun x => activeSet B x = ∅)) := by sorry

end AlgCoverage.OddOrder
