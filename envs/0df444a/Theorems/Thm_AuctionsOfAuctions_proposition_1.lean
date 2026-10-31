-- Prove2me | Theorems.Thm_AuctionsOfAuctions_proposition_1
-- name    : AuctionsOfAuctions.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:28.522911+00:00
-- url     : https://prove2.me/theorems/98cb156e-f326-42fe-a38a-c21859e51a9c
-- title:
--   Proposition 1 (Upward Reserve Price Distortion): $R^{ex}\tilde\lambda(R^{ex})=1$, $\tilde\lambda<\lambda_1$, $R^{ex}>R^{dir}$ (corrected: $\tilde\lambda$ increasing under $\lambda_1$ increasing)
-- statement:
--   Let $F$ be a regular valuation distribution on $[0,1]$, $\pi^{dir}_P$ and $\pi^{ex}_P$ the publisher's revenues (4) and (18), $\lambda_1(x)=f(x)/(1-F(x))$, and
--   $$\tilde\lambda(x)=\frac{2F(x)f(x)}{[1-F(x)][3-F(x)]}\qquad(19).$$
--
--   1. Every maximizer $R^{ex}$ of $\pi^{ex}_P$ over $[0,1]$ lies in $(0,1)$ and satisfies $R^{ex}\tilde\lambda(R^{ex})=1$.
--   2. $\tilde\lambda(x)<\lambda_1(x)$ for every $x\in(0,1)$.
--   3. For every maximizer $R^{dir}$ of $\pi^{dir}_P$ and every maximizer $R^{ex}$ of $\pi^{ex}_P$ over $[0,1]$,
--   $$R^{dir}<R^{ex}.$$
--   4. If moreover $\lambda_1$ is strictly increasing on $(0,1)$, then $\tilde\lambda$ is strictly increasing on $[0,1)$.
--
--   The presence of competing exchanges pushes the publisher's optimal reserve price above the direct (Myerson) reserve; this is the paper's core result and the source of the efficiency loss.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: $F$ regular: $\psi(x)=x-(1-F(x))/f(x)$ "is increasing" (p.7) → $\psi$ weakly increasing on $(0,1)$ (MonotoneOn); reason: weak monotonicity is Myerson's regularity; the strict reading is a special case, and $\psi$ is defined where $f>0$
--   - encoding: a reserve price $R$ → $R\in[0,1]$; reason: valuations lie in $[0,1]$: a reserve below $0$ acts as $0$ and a reserve above $1$ sells nothing, so the publisher's choice set is $[0,1]$
--   - generalization: the optimal reserve price $R^{ex}$ (and $R^{dir}$), written as if unique → every maximizer on $[0,1]$ of the transcribed revenue (IsMaxOn); no uniqueness, interiority or first-order condition assumed; reason: when the maximizer is unique this is the paper's statement; under weak regularity maximizers need not be unique
--   - correction: "$\tilde\lambda$ is the following increasing function" (for every regular $F$) → $\tilde\lambda$ strictly increasing on $[0,1)$ when $\lambda_1$ is strictly increasing on $(0,1)$ (clause 4); reason: false for some regular $F$: the distribution with $1/\lambda_1(x)=(1-x)(0.05(1-x)+4x^2(1-x)+x^3)$ has a density that is continuous and positive on $[0,1]$ ($f(0)=20$, $f(1^-)\approx0.034$) and is regular (the derivative of $1/\lambda_1$ stays below $0.81<1$), but $\tilde\lambda\approx10.41,6.46,4.31,3.36,3.00$ at $x=0.1,\dots,0.5$; the paper's proof (A23)–(A25) uses (A8), i.e. $\lambda_1$ increasing, the hypothesis of Claim 1
--   - reading: "$\tilde\lambda(x)<\lambda_1(x)$" → for every $x\in(0,1)$; reason: at $x=0$, $\tilde\lambda(0)=0$ and $\lambda_1(0)=f(0)$ may be $0$; at $x=1$ both are undefined
--   - reading: "$R^{ex}$ satisfies $R^{ex}\tilde\lambda(R^{ex})=1$" → $R^{ex}\in(0,1)$ and $R^{ex}\tilde\lambda(R^{ex})=1$; reason: interiority is where $\tilde\lambda$ is defined and is part of the claim that the maximizer solves the equation
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §4.2, Proposition 1, eq. (19), p.16 (PDF 17); proof A1.4, pp.39–40

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Proposition 1 (Upward Reserve Price Distortion)**, Zeithammer–Choi, *Auctions of Auctions*,
Management Science (2024), doi:10.1287/mnsc.2024.05233, §4.2, p.16 (PDF 17). For a regular
valuation distribution:
(a) every maximizer `R^ex` of `π^ex_P` over `[0, 1]` lies in `(0, 1)` and satisfies
`R^ex λ̃(R^ex) = 1`, with the pseudo hazard `λ̃` of (19);
(b) `λ̃(x) < λ_1(x)` for every `x ∈ (0, 1)`;
(c) `R^dir < R^ex` for every maximizer `R^dir` of `π^dir_P` and every maximizer `R^ex` of
`π^ex_P` over `[0, 1]`;
(d) (corrected) if moreover `λ_1` is strictly increasing on `(0, 1)`, then `λ̃` is strictly
increasing on `[0, 1)`.

**Formalization Note.**
* "The optimal reserve price" is any maximizer on `[0, 1]` (`IsMaxOn`); uniqueness is not assumed.
* The page calls `λ̃` "increasing" for every regular `F`; this is false (a regular `F` with
  `1/λ_1(x) = (1 − x)(0.05(1 − x) + 4x²(1 − x) + x³)`, whose density is continuous on `[0, 1]`
  and positive there, has `λ̃ ≈ 10.41, 6.46, 4.31, 3.36, 3.00` at `x = 0.1, …, 0.5`). Clause (d) adds the hypothesis of Claim 1 (`λ_1` increasing), which the
  paper's proof (A23)–(A25) uses through (A8). -/
theorem proposition_1 (D : ValuationDist) (hreg : D.IsRegular) :
    (∀ Re ∈ Set.Icc (0 : ℝ) 1, IsMaxOn D.revEx (Set.Icc 0 1) Re →
      Re ∈ Set.Ioo (0 : ℝ) 1 ∧ Re * D.lamTilde Re = 1) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, D.lamTilde x < D.lam 1 x) ∧
    (∀ Rd ∈ Set.Icc (0 : ℝ) 1, ∀ Re ∈ Set.Icc (0 : ℝ) 1,
      IsMaxOn D.revDir (Set.Icc 0 1) Rd → IsMaxOn D.revEx (Set.Icc 0 1) Re → Rd < Re) ∧
    (StrictMonoOn (D.lam 1) (Set.Ioo 0 1) → StrictMonoOn D.lamTilde (Set.Ico 0 1)) := by sorry

end AuctionsOfAuctions
