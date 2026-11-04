-- Prove2me | Theorems.Thm_CappedBaseStock_scan_excess_certificate_bound
-- name    : CappedBaseStock.scan_excess_certificate_bound
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:23:09.167+00:00
-- url     : https://prove2.me/theorems/6528a5d1-d9f5-421a-a144-61d4cd24b7a6
-- title:
--   The two certificate constraints bound scan overload
-- statement:
--   Let demand be i.i.d. and nonnegative with finite positive mean $\mu$, and let $L\ge1$. For a demand block define
--
--   $$I_r^m=\max_{0\le k\le m}\sum_{i=0}^{k-1}(r-D_i).$$
--
--   Suppose $0\le r\le\mu$, $z\ge0$, and the two certificate constraints hold:
--
--   $$\mathbb E\!\left[\left(I_r^m+\sum_{i=0}^{m-1}(D_i-r)-z\right)^+\right]\le m(\mu-r),\qquad m\in\{L,L+1\}.$$
--
--   For $V_L=\max_{0\le j\le L}\sum_{i=0}^{L}D_{j+i}$, the scan overload satisfies
--
--   $$\mathbb E\!\left[\left(V_L-((L+1)r+2z)\right)^+\right]\le(2L+1)(\mu-r).$$
--
--   This is a demand-only inequality: it does not presume any stationary inventory distribution or policy cost comparison. Both horizon constraints are retained. It supplies the explicit scan estimate used in the ordinary-base-stock loss bound.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines), SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Public paper listing: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538. Proof of Lemma `lem-base-stock-loss`, lines 585–609: the suffix/prefix maxima, equation `eq-12`, and the concluding expected scan-excess inequality. The scan is translated to zero-based demand coordinates without changing its law.

import Definitions.Def_CappedBaseStock_BaseStockAnalysis

open MeasureTheory
open scoped ENNReal

namespace CappedBaseStock

theorem scan_excess_certificate_bound (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    (∫⁻ d, scanExcess d c.L (((c.L : ℝ) + 1) * r + 2 * z) ∂demandPathLaw P) ≤
      ENNReal.ofReal ((2 * (c.L : ℝ) + 1) * (mean P - r)) := by sorry

end CappedBaseStock
