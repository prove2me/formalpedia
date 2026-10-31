-- Prove2me | Theorems.Thm_AuctionsOfAuctions_proposition_2
-- name    : AuctionsOfAuctions.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:35.944092+00:00
-- url     : https://prove2.me/theorems/14864e88-500e-42fb-ace1-6820ed221797
-- title:
--   Proposition 2 (Double Marginalization): publisher and advertisers both earn less in the auction of auctions
-- statement:
--   Let $F$ be a regular valuation distribution on $[0,1]$. Let $R^{dir}$ maximize the direct-benchmark revenue $\pi^{dir}_P$ of (4) over $[0,1]$, and let $R^{ex}$ maximize the auction-of-auctions revenue $\pi^{ex}_P$ of (18) over $[0,1]$. Then
--   $$\pi^{ex}_P(R^{ex})<\pi^{dir}_P(R^{dir})\qquad\text{and}\qquad \pi_C(R^{ex})<\pi_C(R^{dir}),$$
--   where $\pi_C(R)=\frac14\int_R^1(M-\beta(M;R))\,dF^4(M)$ is the advertiser's expected profit (5), which by (16) is the advertiser's profit in either arrangement at the reserve the publisher sets there.
--
--   When advertisers bid through competing exchanges that run their own first-price auctions, both the publisher and the advertisers are worse off than under direct bidding, even though the allocation stays efficient at any fixed reserve.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: $F$ regular: $\psi(x)=x-(1-F(x))/f(x)$ "is increasing" (p.7) → $\psi$ weakly increasing on $(0,1)$ (MonotoneOn); reason: weak monotonicity is Myerson's regularity; the strict reading is a special case, and $\psi$ is defined where $f>0$
--   - encoding: a reserve price $R$ → $R\in[0,1]$; reason: valuations lie in $[0,1]$: a reserve below $0$ acts as $0$ and a reserve above $1$ sells nothing, so the publisher's choice set is $[0,1]$
--   - generalization: the optimal reserve price $R^{dir}$ and $R^{ex}$, written as if unique → every maximizer on $[0,1]$ of the transcribed revenue (IsMaxOn); no uniqueness, interiority or first-order condition assumed; reason: when the maximizer is unique this is the paper's statement; under weak regularity maximizers need not be unique
--   - reading: "the expected profits of the advertisers and the publisher are lower in the auction of auctions arrangement" → both strict inequalities $\pi^{ex}_P(R^{ex})<\pi^{dir}_P(R^{dir})$ and $\pi_C(R^{ex})<\pi_C(R^{dir})$, with the advertisers' profit in the auction of auctions given by (5) at $R^{ex}$; reason: strict, as in (20) and the proof A1.7; (16) states that the advertiser's profit is the same function (5) of the reserve in every arrangement, and the per-advertiser profit is a quarter of the advertisers' total
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §4.3, Proposition 2, p.20 (PDF 21); eq. (20), p.19; proof A1.7, p.41 (PDF 42)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Proposition 2 (Double Marginalization)**, Zeithammer–Choi, *Auctions of Auctions*,
Management Science (2024), doi:10.1287/mnsc.2024.05233, §4.3, p.20 (PDF 21): "The expected
profits of the advertisers and the publisher are lower in the auction of auctions arrangement than
in the direct market arrangement."

For a regular valuation distribution, every maximizer `R^dir` of the direct revenue `π^dir_P` (4)
and every maximizer `R^ex` of the auction-of-auctions revenue `π^ex_P` (18) over `[0, 1]` satisfy
`π^ex_P(R^ex) < π^dir_P(R^dir)` and `π_C(R^ex) < π_C(R^dir)`, where `π_C` is the advertiser's
expected profit (5), which by (16) is the advertiser's profit in either arrangement.

**Formalization Note.** Optimal reserves are arbitrary maximizers (`IsMaxOn`) of the transcribed
revenues; neither uniqueness nor a first-order condition is assumed. -/
theorem proposition_2 (D : ValuationDist) (hreg : D.IsRegular) (Rd Re : ℝ)
    (hRd : Rd ∈ Set.Icc (0 : ℝ) 1) (hRe : Re ∈ Set.Icc (0 : ℝ) 1)
    (hmaxd : IsMaxOn D.revDir (Set.Icc 0 1) Rd) (hmaxe : IsMaxOn D.revEx (Set.Icc 0 1) Re) :
    D.revEx Re < D.revDir Rd ∧ D.advertiserProfit Re < D.advertiserProfit Rd := by sorry

end AuctionsOfAuctions
