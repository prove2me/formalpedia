-- Prove2me | Theorems.Thm_AuctionsOfAuctions_revenue_ranking_fixed_reserve
-- name    : AuctionsOfAuctions.revenue_ranking_fixed_reserve
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:26.085621+00:00
-- url     : https://prove2.me/theorems/abdc8c4e-fac0-44ef-b553-58a50f2ef990
-- title:
--   §4.1: at a fixed reserve, $\pi^{mono}_P(R)<\pi^{ex}_P(R)<\pi^{dir}_P(R)$ (corrected: $M>R$, $R<1$)
-- statement:
--   For every reserve $R\in[0,1)$:
--
--   1. for every $M\in(R,1]$, the bids the publisher faces satisfy
--   $$R=\gamma^{mono}(M;R)<\gamma^{ex}(M;R)=\tilde\sigma(M;R)<\gamma^{dir}(M;R)=\beta(M;R);$$
--   2. the publisher's revenues satisfy
--   $$\pi^{mono}_P(R)<\pi^{ex}_P(R)<\pi^{dir}_P(R),$$
--   with $\pi^{mono}_P(R)=R(1-F^4(R))$ of (8), $\pi^{ex}_P(R)=\int_R^1\tilde\sigma(M;R)\,dF^4(M)$ of (18) and $\pi^{dir}_P(R)=\int_R^1\beta(M;R)\,dF^4(M)$ of (4).
--
--   At any fixed reserve the competing-exchange arrangement is less profitable for the publisher than direct bidding and more profitable than a monopoly exchange. With the optimality of the direct reserve this gives the publisher's half of Proposition 2.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: the standing assumption that $F$ is regular (p.7) → not assumed; reason: the statement holds for every distribution of the model; regular distributions are instances
--   - correction: "for every $M\ge R$, $R=\gamma^{mono}(M;R)<\gamma^{ex}(M;R)<\gamma^{dir}(M;R)$" → for every $M\in(R,1]$; reason: at $M=R$ all three bids equal $R$ (any $F$, any $R\in(0,1)$), so the strict inequalities fail there
--   - correction: "for any fixed reserve price" → $R\in[0,1)$; reason: at $R=1$ (and any $R\ge1$) the impression is never sold and all three revenues are $0$, so the strict ranking fails
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §4.1, text after eq. (18), p.16 (PDF 17)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Revenue ranking at a fixed reserve**, Zeithammer–Choi, *Auctions of Auctions*, Management
Science (2024), doi:10.1287/mnsc.2024.05233, §4.1, text after (18), p.16 (PDF 17): "for every
`M ≥ R`, `R = γ^mono(M; R) < γ^ex(M; R) < γ^dir(M; R)`. It follows that, for any fixed reserve
price, the exchange mechanism is less profitable for the publisher than the direct mechanism, but
more profitable than the monopoly benchmark".

For every reserve `R ∈ [0, 1)`:
(1) for every `M ∈ (R, 1]`, `R < σ̃(M; R) < β(M; R)` (the bids the publisher faces with a monopoly
exchange, `γ^mono = R`, with competing exchanges, `γ^ex = σ̃`, and directly, `γ^dir = β`);
(2) `π^mono_P(R) < π^ex_P(R) < π^dir_P(R)`, with `π^mono_P` of (8), `π^ex_P` of (18) with
`γ^ex = σ̃`, and `π^dir_P` of (4).

**Formalization Note.** At `M = R` all three bids equal `R`, so the pointwise ranking is strict
only for `M > R`. At `R = 1` the item is never sold and all three revenues are `0`, so the strict
ranking is stated for `R < 1`. -/
theorem revenue_ranking_fixed_reserve (D : ValuationDist) (R : ℝ) (hR : R ∈ Set.Ico (0 : ℝ) 1) :
    (∀ M ∈ Set.Ioc R 1, R < D.sigmaTilde M R ∧ D.sigmaTilde M R < D.beta M R) ∧
    D.revMono R < D.revEx R ∧ D.revEx R < D.revDir R := by sorry

end AuctionsOfAuctions
