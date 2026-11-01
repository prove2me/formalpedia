-- Prove2me | Theorems.Thm_AssignToSeatRM_theorem_3_bid_prices
-- name    : AssignToSeatRM.theorem_3_bid_prices
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:36.580817+00:00
-- url     : https://prove2.me/theorems/0c9a9537-c9eb-4266-b0f6-2270a6e2055c
-- title:
--   Theorem 3 — optimal bid-prices of (6) give optimal maximal-sequence bid-prices $\beta^\dagger_{uv}=\min_k\sum_{\ell=u}^v\beta_{k\ell}$ of (12)
-- statement:
--   Let $C\in\{0,1\}^{N\times M}$ with $N\ge1$, prices $p_{ij}\ge0$ and expected demands $\lambda_{ij}\ge0$. Let $(z,\beta)$ be an optimal solution of the bid-price LP (6). Define
--
--   $$\beta^\dagger_{uv}=\min_{k\in[N]}\sum_{\ell=u}^{v}\beta_{k\ell}\quad(u\le v),\qquad \beta^\dagger_{uv}=0\quad(u>v).$$
--
--   Then there is $z^\dagger$ such that $(z^\dagger,\beta^\dagger)$ is an optimal solution of the maximal-sequence bid-price LP (12) with $A=f(C)$, the vector of maximal-sequence counts of $C$.
--
--   So the nonlinear bid-prices of maximal sequences (policy BPC-M) can be read off the seat-leg bid-prices of the static dual (policy BPC-S); the proof also shows that (6) and (12) have the same optimal value.
--
--   Differences from the source:
--   - generalization: λ_{ij} = λ^{[t,T]}_{ij} for a period t ∈ [T] → any vector λ_{ij} ≥ 0; reason: λ^{[t,T]} is nonnegative, so the source's statement is the special case; t plays no other role in the statement
--   - reading: 'any group of bid-prices {β^t_{kℓ}} in (6)' and 'a group of bid-prices {β^{†t}_{uv}} in (12)' → an optimal solution (z, β) of (6) and an optimal solution (z†, β†) of (12) with A = f(C); reason: bid-prices are obtained by solving (6), resp. (12) (Algorithms 1 and 2), and the proof (pp.ec14–ec15) establishes optimality of the constructed solution
--   - encoding: min_{k ∈ [N]} → hypothesis 0 < N and Finset.inf' over Fin N; reason: the minimum is undefined for N = 0; excludes only that case
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: legs 1..M, itineraries i ≤ j, C ∈ {0,1}^{N×M} with C_{k0} = C_{k(M+1)} = 0 → natural-number indices with explicit bounds (itins M); C : Fin N → Fin M → Bool read through cap, which is false outside 1..M; reason: Lean convention; same instances
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Theorem 3 and (13), p.17; proof pp.ec14–ec15

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_BidPriceLP
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Theorem 3** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.17, (13)): for any capacity matrix `C` and any group of bid-prices
`{β_{kℓ}}` of (6) (an optimal solution `(z, β)` of (6)) there is a group of bid-prices `{β†_{uv}}`
of (12) (an optimal solution `(z†, β†)` of (12) with `A = f(C)`) such that
`β†_{uv} = min_{k ∈ [N]} Σ_{ℓ: u ≤ ℓ ≤ v} β_{kℓ}` for all `u ≤ v`.

**Formalization Note.** The expected demands `λ_{ij}` of both objectives are any nonnegative
vector (the paper's `λ^{[t,T]}_{ij}`; the period `t` plays no other role). The minimum over
`k ∈ [N]` requires `N ≥ 1`; `β†_{uv} = 0` for `u > v` is the convention of (12). Prices are
nonnegative (fares). -/
theorem theorem_3_bid_prices {N M : ℕ} (hN : 0 < N) (C : CapMat N M) (p : ℕ → ℕ → ℝ)
    (hp : IsPriceVec M p) (lam : ℕ → ℕ → ℝ) (hlam : ∀ ij ∈ itins M, 0 ≤ lam ij.1 ij.2)
    (z : ℕ × ℕ → ℝ) (β : Fin N → ℕ → ℝ) (hopt : IsOptLP6 C p lam z β) :
    ∃ zd : ℕ × ℕ → ℝ,
      IsOptLP12 M p (fun u v => (fC C u v : ℝ)) lam zd (minSeatBidPrice hN β) := by sorry

end AssignToSeatRM
