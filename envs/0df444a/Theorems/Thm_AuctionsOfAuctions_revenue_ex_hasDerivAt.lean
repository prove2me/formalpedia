-- Prove2me | Theorems.Thm_AuctionsOfAuctions_revenue_ex_hasDerivAt
-- name    : AuctionsOfAuctions.revenue_ex_hasDerivAt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:25.315979+00:00
-- url     : https://prove2.me/theorems/d29e170c-7aa2-4d89-bda5-5a4260561f92
-- title:
--   Proof of Proposition 1, (A17)–(A21): $\frac{d}{dR}\pi^{ex}_P(R)=2F^2(R)\,[(1-F(R))(3-F(R))-2RF(R)f(R)]$
-- statement:
--   For every reserve $R\in(0,1)$, the publisher's revenue in the auction of auctions, $\pi^{ex}_P(R)=\int_R^1\tilde\sigma(M;R)\,dF^4(M)$ of (18), is differentiable at $R$ with
--   $$\frac{d}{dR}\pi^{ex}_P(R)=2F^2(R)\Big[(1-F(R))(3-F(R))-2RF(R)f(R)\Big].$$
--   For $R\in(0,1)$ the sign of the derivative is the sign of $1-R\tilde\lambda(R)$, with $\tilde\lambda$ of (19); this locates the optimal reserve of the auction of auctions (Proposition 1).
--
--   **Formalization Note** The paper differentiates (A17), "dropping the constant multiplier 2", and evaluates the result in (A18)–(A20) as $-2F(R)f(R)\,RF^2(R)+F^2(R)(1-F(R))(3-F(R))$; the statement gives the derivative of $\pi^{ex}_P$ itself, twice that expression.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: the standing assumption that $F$ is regular (p.7) → not assumed; reason: the statement holds for every distribution of the model; regular distributions are instances
--   - reading: (A21): "(A18) $=0\Leftrightarrow 2F(R)f(R)R=(1-F(R))(3-F(R))\Leftrightarrow R=\{x:1-x\lambda^{ex}(x)=0\}$" → the derivative of $\pi^{ex}_P$ at every $R\in(0,1)$ equals $2F^2(R)[(1-F(R))(3-F(R))-2RF(R)f(R)]$; reason: (A21) summarizes the computation (A18)–(A20) of the derivative (up to the dropped factor 2); the derivative is that computation's content and implies the equivalence for $R\in(0,1)$
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, proof of Proposition 1, eqs. (A16)–(A21), p.39 (PDF 40)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Derivative of the publisher's revenue in the auction of auctions**, Zeithammer–Choi,
*Auctions of Auctions*, Management Science (2024), doi:10.1287/mnsc.2024.05233, proof of
Proposition 1, eqs. (A16)–(A21), p.39 (PDF 40): for every reserve `R ∈ (0, 1)`,
`d π^ex_P / dR = 2 F(R)² [(1 − F(R))(3 − F(R)) − 2 R F(R) f(R)]`.

**Formalization Note.** (A18) is the derivative "dropping the constant multiplier 2" of (A17);
by (A19)–(A20) it equals `−2F(R)f(R)·RF²(R) + F²(R)(1 − F(R))(3 − F(R))`. The statement is the
derivative of `π^ex_P` itself, i.e. twice that expression. -/
theorem revenue_ex_hasDerivAt (D : ValuationDist) (R : ℝ) (hR : R ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt D.revEx
      (2 * D.F R ^ 2 * ((1 - D.F R) * (3 - D.F R) - 2 * R * D.F R * D.f R)) R := by sorry

end AuctionsOfAuctions
