-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_lemma_6_1
-- name    : AlgCoverage.OddOrder.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:38.587032+00:00
-- url     : https://prove2.me/theorems/e3c018f4-2e19-4803-aef8-b02a206bab14
-- title:
--   Lemma 6.1 — unweighted full-word upper bound $\Pr_X(W_U=z,\ \mathrm{FULL}(U))\le N^{-j}$
-- statement:
--   Let $G$ be a finite group of odd order $N$ with a supplied $G$-normal elementary-abelian series (6.1), and let $X=(X_1,\dots,X_k)$ be iid uniform inputs. For every fixed selector array $U=(v_1,\dots,v_j)$, including empty and repeated rows, and every fixed target array $z\in G^j$,
--   $$\Pr_X\big(W_{v_a}=z_a\ \text{for all } a,\ \ \mathrm{FULL}(U)\big)\le N^{-j}. \tag{6.2}$$
--   The probability is over the full original input tuple at fixed masks; it is not conditioned on anything.
--
--   Differences from the source:
--   - encoding: a supplied G-normal elementary-abelian series (6.1) and FULL as surjectivity of the coefficient map at every layer → s : NormalEASeries G (0-based layers A (r+1)/A r, every layer nontrivial: d_r ≥ 1) and FULL s x U: every target in A_{r+1}^j is hit modulo A_r by the layer word ∏ P_i a_i P_i⁻¹ for some lifts a ∈ A_{r+1}^k; reason: the layer quotient is abelian and normal in G/A_r, so this is surjectivity of the induced linear coefficient map with coefficients θ(prefix) of form (5.1); d_r ≥ 1 is the reading of (6.1) declared in eq_6_1 (J ≤ log₃ N needs it), and a series with trivial layers collapses to one without them with the same FULL and no larger J
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 21 (PDF 22), Lemma 6.1, Eq. (6.2)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Series

namespace AlgCoverage.OddOrder

/-- Lemma 6.1 (unweighted full-word upper bound), Lin, printed p. 21 / PDF 22. `G` of odd order `N`
with a supplied series (6.1); for every fixed selector array `U` of `j` rows (empty and repeated rows
allowed) and every fixed target array `z ∈ G^j`, over iid uniform inputs `X ∈ G^k`:
`Pr_X(W_U = z, FULL(U)) ≤ N^{−j}` (6.2). -/
theorem lemma_6_1 (G : Type*) [Group G] [Fintype G] (hodd : Odd (Fintype.card G))
    (s : NormalEASeries G) (j k : ℕ) (U : Fin j → Fin k → Bool) (z : Fin j → G) :
    probIid G k (fun x => (∀ a, word x (U a) = z a) ∧ FULL s x U) ≤
      1 / (Fintype.card G : ℝ) ^ j := by sorry

end AlgCoverage.OddOrder
