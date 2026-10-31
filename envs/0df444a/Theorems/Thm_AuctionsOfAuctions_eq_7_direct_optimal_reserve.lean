-- Prove2me | Theorems.Thm_AuctionsOfAuctions_eq_7_direct_optimal_reserve
-- name    : AuctionsOfAuctions.eq_7_direct_optimal_reserve
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:24.720777+00:00
-- url     : https://prove2.me/theorems/9f7d26af-5ec1-4ab6-82a5-12dabaa42919
-- title:
--   Eq. (7): every optimal reserve of the direct benchmark solves $\psi(R)=0$, i.e. $R\lambda_1(R)=1$
-- statement:
--   Let $F$ be a regular valuation distribution on $[0,1]$ and let $\pi^{dir}_P(R)=\int_R^1\beta(M;R)\,dF^4(M)$ be the publisher's expected revenue (4) when the four advertisers bid directly in the first-price auction with reserve $R$. If $R\in[0,1]$ maximizes $\pi^{dir}_P$ over $[0,1]$, then $R\in(0,1)$ and
--   $$\psi(R)=0,\qquad\text{equivalently}\qquad R\,\lambda_1(R)=1,$$
--   where $\psi(x)=x-(1-F(x))/f(x)$ and $\lambda_1(x)=f(x)/(1-F(x))$.
--
--   This is Myerson's characterization of the optimal reserve, applied to the first-price revenue (4); it is the benchmark against which Proposition 1 measures the upward distortion.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: $F$ regular: $\psi(x)=x-(1-F(x))/f(x)$ "is increasing" (p.7) → $\psi$ weakly increasing on $(0,1)$ (MonotoneOn); reason: weak monotonicity is Myerson's regularity; the strict reading is a special case, and $\psi$ is defined where $f>0$
--   - encoding: a reserve price $R$ → $R\in[0,1]$; reason: valuations lie in $[0,1]$: a reserve below $0$ acts as $0$ and a reserve above $1$ sells nothing, so the publisher's choice set is $[0,1]$
--   - generalization: the optimal reserve price $R^{dir}$, written as if unique → every maximizer on $[0,1]$ of the transcribed revenue (IsMaxOn); no uniqueness, interiority or first-order condition assumed; reason: when the maximizer is unique this is the paper's statement; under weak regularity maximizers need not be unique
--   - reading: "the optimal reserve … solves $\psi(R^{dir})=0$, which is equivalent to $R^{dir}\lambda_1(R^{dir})=1$" → $R\in(0,1)$, $\psi(R)=0$ and $R\lambda_1(R)=1$; reason: both equations of the sentence are stated; interiority is where $\psi$ and $\lambda_1$ are defined and is part of the claim that the maximizer solves them
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §3.1, eq. (7), p.10 (PDF 11)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **The direct benchmark's optimal reserve**, eq. (7), Zeithammer–Choi, *Auctions of Auctions*,
Management Science (2024), doi:10.1287/mnsc.2024.05233, §3.1, p.10 (PDF 11): "the publisher's
optimal reserve price that maximizes (4) solves `ψ(R^dir) = 0`, which is equivalent to
`R^dir λ_1(R^dir) = 1`".

For a regular valuation distribution, every maximizer `R` of the direct-benchmark revenue
`π^dir_P` of (4) over `[0, 1]` lies in `(0, 1)` and satisfies `ψ(R) = 0` and `R λ_1(R) = 1`.

**Formalization Note.** "Optimal reserve" is any maximizer of `π^dir_P` on `[0, 1]` (`IsMaxOn`);
nothing is assumed about uniqueness. -/
theorem eq_7_direct_optimal_reserve (D : ValuationDist) (hreg : D.IsRegular) (R : ℝ)
    (hR : R ∈ Set.Icc (0 : ℝ) 1) (hmax : IsMaxOn D.revDir (Set.Icc 0 1) R) :
    R ∈ Set.Ioo (0 : ℝ) 1 ∧ D.psi R = 0 ∧ R * D.lam 1 R = 1 := by sorry

end AuctionsOfAuctions
