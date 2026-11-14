-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_FRP_boundOn
-- name    : BCFGJPSSV26.Greedy.FRP.boundOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:17.286884+00:00
-- url     : https://prove2.me/theorems/f47f12e0-5e92-4404-8a88-b1437ddbabff
-- title:
--   Bound $f+\rho\sum_j d_j$ on the factor-revealing program over a finite linear order
-- statement:
--   This is the bound on the factor-revealing program of [Part I, Definition 4.1 and Theorem 4.4] for the bid $\beta(x,y)=\max(x-\gamma y,0)$ with $\gamma=\frac{153}{125}$, in the form the analysis of the greedy algorithm uses: without normalization, over the rationals, and for clients indexed by any finite linear order.
--
--   Let $\iota$ be a finite linearly ordered set (the clients). The times are $\iota\cup\{\top\}$ with $\top$ above every client, and $k^+$ denotes the successor of $k\in\iota$ among the times (the next client, or $\top$ if $k$ is the last). Let $r_{jt}\in\mathbb{Q}$ for clients $j$ and times $t$, let $d_j\in\mathbb{Q}$ for clients $j$, and let $f\in\mathbb{Q}$, such that
--
--   1. $r_{j,k^+}\le r_{jk}$ for all clients $j\le k$;
--   2. $r_{kk}\le r_{jk}+d_k+d_j$ for all clients $j<k$;
--   3. $r_{jt}\le r_{lt}+d_l+d_j$ for all clients $j,l$ and every time $t$ with $j<t$ and $l<t$;
--   4. $\sum_{j<k}\beta(r_{jk},d_j)+\sum_{j\ge k}\beta(r_{kk},d_j)\le f$ for every client $k$;
--   5. $f\ge 0$, $d_j\ge 0$ and $r_{jt}\ge 0$ for all $j$ and $t$.
--
--   If $\sum_j d_j>0$, then
--
--   $$\sum_{j\in\iota}\Big(\sum_{k\ge j}\beta\big(r_{jk},r_{j,k^+}\big)+r_{j\top}\Big)\;\le\;f+\rho\sum_{j\in\iota}d_j,\qquad \rho=2-(\gamma-1)^2=\tfrac{30466}{15625}=1.949824,$$
--
--   where the inner sum is over the clients $k\ge j$.
--
--   In the proof of the robust LMP guarantee ([Part I, Theorem D.7]) the bound is applied to the point built from the execution of the greedy algorithm for the clients served by one facility of a comparison solution; this is where the ratio $\rho<1.9499$ of Theorems 1.2 and 1.4 comes from.
--
--   **Formalization Note** The paper's program is normalized by $\sum_j d_j=1$, has real variables and clients $1,\dots,n$ with the last time $n+1$; here the normalization is replaced by the factor $\sum_j d_j$ on the right, the variables are rational, and $\top$ plays the role of $n+1$. Constraint 3 is also asked for $j=l$, where it is trivial. The normalized real bound itself is taken from the imported library KMedian195.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 4.4 (program of Definition 4.1). Lean source: `BCFGJPSSV26.Greedy.FRP.boundOn`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/FRP.lean#L248-L255

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Bid
public import Definitions.Def_KMedian195_FactorRevealingPrimal
public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Fin.Basic
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy.FRP

open Finset

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

section finTime

variable {n : ℕ} (e : Fin n ≃o ι)

end finTime

theorem boundOn {r : ι → WithTop ι → ℚ} {d : ι → ℚ} {f : ℚ} (h : FeasibleOn r d f)
    (hd : 0 < ∑ j, d j) : ∑ j, term r j ≤ f + ρ * ∑ j, d j := by sorry

end BCFGJPSSV26.Greedy.FRP
end
