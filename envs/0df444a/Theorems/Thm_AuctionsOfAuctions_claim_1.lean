-- Prove2me | Theorems.Thm_AuctionsOfAuctions_claim_1
-- name    : AuctionsOfAuctions.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:26.079969+00:00
-- url     : https://prove2.me/theorems/d5d88d44-4ade-4c17-be1e-38a59f14b293
-- title:
--   Claim 1: $\lambda_m(x)$ decreases in $m$; $x\lambda_m(x)$ increases in $x$ when $\lambda_1$ increases
-- statement:
--   Let $F$ be a valuation distribution on $[0,1]$ with density $f$, and let $\lambda_m(x)=\dfrac{mF^{m-1}(x)f(x)}{1-F^m(x)}$ be the generalized hazard rate of the maximum of $m$ draws.
--
--   1. For every $x\in(0,1)$, $\lambda_m(x)$ is strictly decreasing in $m\in\{1,2,\dots\}$:
--   $$\lambda_{m+1}(x)<\lambda_m(x)\qquad(m\ge1).$$
--   2. If $\lambda_1(x)=f(x)/(1-F(x))$ is strictly increasing on $(0,1)$, then for every $m\ge1$ the map $x\mapsto x\lambda_m(x)$ is strictly increasing on $[0,1)$.
--
--   Part 1 compares the reserve-price conditions of auctions with different numbers of bidders; part 2 makes each condition $x\lambda_m(x)=1$ have at most one root.
--
--   **Formalization Note** Part 1 is stated for $x\in(0,1)$ and as strict antitonicity on $\{m\in\mathbb N: m\ge1\}$; part 2 assumes strict monotonicity of $\lambda_1$ instead of $\lambda_1'>0$.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - reading: (i) "$\lambda_m(x)$ decreases in $m$ for all fixed $x$" → strictly decreasing in $m\ge1$ for every $x\in(0,1)$; reason: at $x=0$, $\lambda_m(0)=0$ for every $m\ge2$, and at $x=1$ the quotient is undefined; the proof (A1)–(A2) needs $0<F(x)<1$; strict is the stronger reading of "decreases"
--   - reading: (ii) "$x\lambda_m(x)$ increases in $x$" → strictly increasing on $[0,1)$; reason: $\lambda_m$ is undefined at $x=1$; the proof (A7) gives a strictly positive sign
--   - generalization: $F$ regular and $\lambda_1'(x)>0$ → $\lambda_1$ strictly increasing on $(0,1)$ (part 2 only; part 1 has no hypothesis); reason: $\lambda_1'>0$ implies strict increase without assuming $f$ differentiable, and strict increase of $\lambda_1$ implies regularity because $\psi(x)=x-1/\lambda_1(x)$ on $(0,1)$; the page notes regularity is not used for (i)
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, Appendix A1.1, Claim 1, p.36 (PDF 37)

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Claim 1**, Zeithammer–Choi, *Auctions of Auctions*, Management Science (2024),
doi:10.1287/mnsc.2024.05233, Appendix A1.1, p.36 (PDF 37): for the generalized hazard rate
`λ_m(x) = m F^{m−1}(x) f(x)/(1 − F^m(x))` of eq. (1),
(i) `λ_m(x)` is strictly decreasing in `m ≥ 1` for every fixed `x ∈ (0, 1)`;
(ii) if `λ_1` is strictly increasing on `(0, 1)`, then for every `m ≥ 1`, `x ↦ x λ_m(x)` is
strictly increasing on `[0, 1)`.

**Formalization Note.**
* (i) is stated on `(0, 1)`: at `x = 0`, `λ_m(0) = 0` for every `m ≥ 2`, and at `x = 1` the
  quotient is undefined. The page notes that (i) does not use regularity.
* The page's hypothesis "`F` regular with `λ'_1(x) > 0`" is replaced by "`λ_1` strictly
  increasing on `(0, 1)`": `λ'_1 > 0` implies it without assuming `f` differentiable, and it
  implies regularity, since `ψ(x) = x − 1/λ_1(x)` on `(0, 1)`. -/
theorem claim_1 (D : ValuationDist) :
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, StrictAntiOn (fun m : ℕ => D.lam m x) {m : ℕ | 1 ≤ m}) ∧
    (StrictMonoOn (D.lam 1) (Set.Ioo 0 1) →
      ∀ m : ℕ, 1 ≤ m → StrictMonoOn (fun x => x * D.lam m x) (Set.Ico 0 1)) := by sorry

end AuctionsOfAuctions
