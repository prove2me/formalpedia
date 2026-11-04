-- Prove2me | Theorems.Thm_CappedBaseStock_window_jensen_certificate
-- name    : CappedBaseStock.window_jensen_certificate
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:24:35.766218+00:00
-- url     : https://prove2.me/theorems/0e0b5f9a-8948-4f42-a328-177bbc5d1736
-- title:
--   Finite-window Jensen certificate inequality
-- statement:
--   Let $(D_k)$ be i.i.d. nonnegative demands with finite positive mean $\mu$. Let $(I_0,A_0,\ldots,A_{n-1})$ be a nonnegative random vector, independent of the entire demand sequence, with finite first moments and common means
--
--   $$
--   \mathbb E[I_0]=z\ge0,\qquad
--   \mathbb E[A_i]=r\quad(0\le i<n),\qquad 0\le r\le\mu.
--   $$
--
--   Dependence among the input coordinates is allowed. Define $I_{k+1}=(I_k+A_k-D_k)^+$, and choose an integer horizon $1\le m\le n$ for which $\mathbb E[I_m]\le z$. For a fresh demand block define the finite constant-order envelope
--
--   $$
--   J_r^m=\max_{0\le k\le m}\sum_{i=0}^{k-1}(r-D_i),
--   $$
--
--   where the empty sum is zero. Then
--
--   $$
--   \mathbb E\!\left[\left(J_r^m+\sum_{i=0}^{m-1}(D_i-r)-z\right)^+\right]
--   \le m(\mu-r).
--   $$
--
--   This finite-window Jensen certificate lemma converts an expected-inventory upper bound into one constraint of the lower-certificate optimization problem. It applies independently at horizons $L$ and $L+1$ and makes no assertion about an optimal policy or its existence.
--
--   **Formalization Note** The nonnegative expectation is a Lebesgue integral in the extended nonnegative reals. The explicit first-moment assumptions and product demand law retain the integrability and independence needed for the finite-window statement.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, user-supplied 2026 manuscript, Proposition 1 (label lemma-lb), source-manuscript.tex lines 253-303; SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Equation eq-envelope-expectation at source lines 214-222 and the conditional Jensen argument at lines 277-300; auxiliary general finite-window formulation of those two steps, with independence and first moments explicit. Related background: Xin and Goldberg, Optimality Gap of Constant-Order Policies Decays Exponentially in the Lead Time for Lost Sales Models, Operations Research 64(6), 1556-1565 (2016), DOI 10.1287/opre.2016.1514; author-hosted April 2016 manuscript https://people.orie.cornell.edu/dag369/ftp/Goldberg_Xin_Lost_Sales_Constant_Order_Expofast_4_2016.pdf, Theorem 2 on printed page 9, Observation 1 on printed page 10, and Appendix 5.3. Observation 1 motivates the finite-window Jensen step; the iid reversal identity is explicitly present in the supplied manuscript.

import Definitions.Def_CappedBaseStock_Window

open MeasureTheory
open scoped ENNReal

namespace CappedBaseStock

theorem window_jensen_certificate (P : DemandLaw) (n : ℕ) (W : WindowLaw n)
    (r z : ℝ) (hr : 0 ≤ r) (hrmean : r ≤ mean P) (hz : 0 ≤ z)
    (hmeans : WindowMeans W r z) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hbound : windowExpectedInventory P W m ≤ ENNReal.ofReal z) :
    (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r)) := by sorry

end CappedBaseStock
