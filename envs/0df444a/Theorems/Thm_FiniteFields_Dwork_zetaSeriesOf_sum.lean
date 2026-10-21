-- Prove2me | Theorems.Thm_FiniteFields_Dwork_zetaSeriesOf_sum
-- name    : FiniteFields.Dwork.zetaSeriesOf_sum
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T02:03:28.308558+00:00
-- url     : https://prove2.me/theorems/71a1d934-47b3-4847-b3b0-6a52303f14b0
-- title:
--   Zeta series of a sum of counts: $Z_{\sum_i N_i} = \prod_i Z_{N_i}$
-- statement:
--   For a sequence $N = (N_s)_{s \ge 1}$ of natural numbers, its **zeta series** is the formal power series
--   $$Z_N(t) = \exp\Big(\sum_{s \ge 1} \frac{N_s}{s}\, t^s\Big) \in \mathbb{Q}[[t]],$$
--   the formal exponential of a series with zero constant term; in particular $Z_N(0) = 1$.
--
--   **Statement.** Let $S$ be a finite set and let $(N_i)_{i \in S}$ be a family of sequences of natural numbers. Then
--   $$Z_{\sum_{i \in S} N_i}(t) \;=\; \prod_{i \in S} Z_{N_i}(t),$$
--   where $\sum_{i \in S} N_i$ is the termwise sum $s \mapsto \sum_{i \in S} N_{i,s}$. For $S = \emptyset$ both sides equal $1$.
--
--   When $N_i$ is the point-count sequence of a piece $V_i$ of a finite decomposition of a variety $V$ into disjoint locally closed subsets, $\sum_i N_i$ is the point-count sequence of $V$; the identity then says that the zeta function of $V$ is the product of the zeta functions of the pieces. This multiplicativity is used in the reductions of §3 and in the inclusion–exclusion argument of §5.
--
--   **Formalization Note.** Lean indexes $s = n+1$ by $n \in \mathbb{N}$: `zetaSeriesOf N` is the formal exponential (substitution into `PowerSeries.exp ℚ`) of $\sum_{n \ge 0} N(n)\, t^{n+1}/(n+1)$. The sequences are arbitrary maps $\mathbb{N} \to \mathbb{N}$, not necessarily point counts, and $S$ is a `Finset` in an arbitrary index type.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, Introduction (definition $\zeta(V;t) = \exp(\sum_{s \ge 1} N_s t^s/s)$); the multiplicativity is used in the reductions (15) of §3 and in the inclusion–exclusion of §5, Application 2. Auxiliary formal identity in the formalization; not stated separately in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/AffineHypersurfaceRationality/ZetaCalculus.lean`, declaration `WeilConjectures.Dwork.zetaSeriesOf_sum`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Meromorphy

open PowerSeries
open FiniteFields.Dwork

theorem FiniteFields.Dwork.zetaSeriesOf_sum {ι : Type*} (s : Finset ι) (N : ι → ℕ → ℕ) :
    zetaSeriesOf (fun n ↦ ∑ i ∈ s, N i n) = ∏ i ∈ s, zetaSeriesOf (N i) := by sorry
