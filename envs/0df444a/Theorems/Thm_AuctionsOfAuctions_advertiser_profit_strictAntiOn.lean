-- Prove2me | Theorems.Thm_AuctionsOfAuctions_advertiser_profit_strictAntiOn
-- name    : AuctionsOfAuctions.advertiser_profit_strictAntiOn
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:37.310388+00:00
-- url     : https://prove2.me/theorems/8448b32d-e8ea-4bf7-adc0-f2e774012042
-- title:
--   Footnote 24 and (16): the advertiser's profit $\pi_C$ is strictly decreasing in the reserve
-- statement:
--   The advertiser's ex ante expected profit
--   $$\pi_C(R)=\frac14\int_R^1\big(M-\beta(M;R)\big)\,dF^4(M)$$
--   of (5), which by (16) is the advertiser's profit in every arrangement as a function of the reserve the publisher sets, is strictly decreasing on $[0,1]$: $\pi_C(R')<\pi_C(R)$ whenever $0\le R<R'\le1$.
--
--   Since the exchanges leave the advertisers' bids and allocation unchanged, the advertisers' welfare depends on the arrangement only through the reserve price; with Proposition 1 this gives the advertisers' half of Proposition 2.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: the standing assumption that $F$ is regular (p.7) → not assumed; reason: the statement holds for every distribution of the model; regular distributions are instances
--   - encoding: a reserve price $R$ → $R\in[0,1]$; reason: valuations lie in $[0,1]$: a reserve below $0$ acts as $0$ and a reserve above $1$ sells nothing, so the publisher's choice set is $[0,1]$
--   - reading: "$\pi_C$ decreases in reserve" → strictly decreasing on $[0,1]$; reason: strict is the stronger reading, and the proof of Proposition 2 needs it to conclude a strict loss
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, footnote 24, p.25 (PDF 26); eqs. (5) and (16), pp.10, 15; used in the proof of Proposition 2, A1.7, p.41 (PDF 42)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Advertiser profit decreases in the reserve**, Zeithammer–Choi, *Auctions of Auctions*,
Management Science (2024), doi:10.1287/mnsc.2024.05233, footnote 24, p.25 (PDF 26): "`π_C`
decreases in reserve", for the advertiser's ex ante profit `π_C` of (5)/(16) (pp.10, 15); used in
the proof of Proposition 2, A1.7, p.41 (PDF 42). Stated strictly on `[0, 1]`.

**Formalization Note.** "Decreases" is read as strictly decreasing on all reserves `R ∈ [0, 1]`. -/
theorem advertiser_profit_strictAntiOn (D : ValuationDist) :
    StrictAntiOn D.advertiserProfit (Set.Icc 0 1) := by sorry

end AuctionsOfAuctions
