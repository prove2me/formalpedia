-- Prove2me | Theorems.Thm_AuctionsOfAuctions_lemma_2_shading
-- name    : AuctionsOfAuctions.lemma_2_shading
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:31.275538+00:00
-- url     : https://prove2.me/theorems/9814caba-b246-4d06-9b9e-d94089bf5de5
-- title:
--   Lemma 2, eq. (14): exchanges shade more, $\tilde\sigma(m;R)<\beta(m;R)$ for $m>R$ (corrected: $m>R$)
-- statement:
--   For every reserve $R\in[0,1]$ and every type $m\in(R,1]$, the exchanges' bid (13) lies strictly below the advertisers' bid (3):
--   $$\tilde\sigma(m;R)<\beta(m;R).$$
--
--   Exchanges bid as if facing two rivals and valuing the impression at the pseudo-valuations $\beta(y;R)$, so they shade more than the advertisers; this is the first of the two sources of double marginalization.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: the standing assumption that $F$ is regular (p.7) → not assumed; reason: the statement holds for every distribution of the model; regular distributions are instances
--   - encoding: a reserve price $R$ → $R\in[0,1]$; reason: valuations lie in $[0,1]$: a reserve below $0$ acts as $0$ and a reserve above $1$ sells nothing, so the publisher's choice set is $[0,1]$
--   - correction: (14) $\tilde\sigma(m;R)<\beta(m;R)$, printed without a domain → for $m\in(R,1]$; reason: at $m=R$ both bids equal $R$ for every $F$ and every $R\in(0,1]$, so the strict inequality fails there; the OA8 proof states it "for all $m>R$"
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §3.3, Lemma 2, eq. (14), p.13 (PDF 14); direct proof OA8, OA p.14 (PDF 60)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Lemma 2, eq. (14): exchanges shade more than advertisers**, Zeithammer–Choi, *Auctions of
Auctions*, Management Science (2024), doi:10.1287/mnsc.2024.05233, §3.3, p.13 (PDF 14); direct
proof in OA8, OA p.14 (PDF 60): `σ̃(m; R) < β(m; R)` for every reserve `R ∈ [0, 1]` and every type
`m ∈ (R, 1]`.

**Formalization Note.** (14) is printed without a domain; at `m = R` both bids equal `R`, so the
strict inequality holds exactly for `m > R` (the OA8 proof says "for all `m > R`"). -/
theorem lemma_2_shading (D : ValuationDist) (R : ℝ) (hR : R ∈ Set.Icc (0 : ℝ) 1) :
    ∀ m ∈ Set.Ioc R 1, D.sigmaTilde m R < D.beta m R := by sorry

end AuctionsOfAuctions
