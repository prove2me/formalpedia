-- Prove2me | Theorems.Thm_DraftPoA_lemma_3_2
-- name    : DraftPoA.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:57.481411+00:00
-- url     : https://prove2.me/theorems/e0809171-d637-447e-a08c-03cfc02cd78f
-- title:
--   Lemma 3.2 (Covering lemma): $\sum_{t=0}^{\tau}\Phi(p_t)\ge(1-\varepsilon)V-\rho\sum_{j\in S}\pi_j-2k\delta$
-- statement:
--   Let $v$ be a normalized, monotone, subadditive valuation and $S$ a set of $k\ge1$ items with $V=v(S)>0$; give each $j\in S$ a price $\pi_j\ge0$ and let
--
--   $$\Phi(p)=\max\{\,v(U)-p|U|\;:\;U\subseteq S,\ \pi_j<p\text{ for all }j\in U\,\}.$$
--
--   Fix $\rho>1$, $\varepsilon\in(0,1)$, the bottom rung $\theta=\varepsilon V/k$ and an integer $\tau\ge\log_\rho(k/\varepsilon)$. If the prices satisfy $\theta\rho^t\le p_t\le\theta\rho^t+\delta$ for $t=0,\dots,\tau$, with $\delta\ge0$, then
--
--   $$\sum_{t=0}^{\tau}\Phi(p_t)\ \ge\ (1-\varepsilon)V-\rho\sum_{j\in S}\pi_j-2k\delta.$$
--
--   This is where the rate $\ln m/\ln\ln m$ comes from: one price cannot account for the whole value of a bundle, but a geometric ladder of $\tau+1$ prices does, up to a charge of $\rho$ times what the items cost.
--
--   **Formalization Note** $S$ is a finite set of items `Fin m` and $v$ is defined on all subsets (a valuation on $S$ extends by $T\mapsto v(T\cap S)$); only subsets of $S$ enter the statement.
--
--   Differences from the source:
--   - encoding: v a valuation on the set S → v a valuation on the subsets of Fin m, S a Finset; reason: every valuation on S extends by T ↦ v(T ∩ S); only subsets of S occur
--   - encoding: τ an integer with τ ≥ log_ρ(k/ε) → τ : ℕ; reason: log_ρ(k/ε) > 0 since k/ε > 1 and ρ > 1, so such τ is a natural number
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Lemma 3.2, p.7 (PDF 8); proof App. A.2, pp.16–17 (PDF 17–18)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_DraftPoA_Activation

open ComplementFreeCA.CFRounding

namespace DraftPoA

/-- Lemma 3.2 (Covering lemma), p.7 (PDF 8); proof App. A.2, pp.16–17 (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

Let `v` be a normalized monotone subadditive valuation and `S` a set of `k ≥ 1` items with
`V = v(S) > 0`; give each `j ∈ S` a price `π_j ≥ 0` and let
`Φ(p) = max{ v(U) − p|U| : U ⊆ S, π_j < p for all j ∈ U }`. Fix `ρ > 1`, `ε ∈ (0, 1)`, the bottom
rung `θ = εV/k` and an integer `τ ≥ log_ρ(k/ε)`. If `θρ^t ≤ p_t ≤ θρ^t + δ` for `t = 0, …, τ` with
`δ ≥ 0`, then `Σ_{t=0}^{τ} Φ(p_t) ≥ (1 − ε)V − ρ Σ_{j∈S} π_j − 2kδ`.

**Formalization Note.** The items are a `Finset` `S` of `Fin m` and `v` is a valuation on all
subsets of `Fin m` (any valuation on `S` extends by `T ↦ v(T ∩ S)`); only subsets of `S` enter
the statement. `τ` is a natural number: an integer `τ ≥ log_ρ(k/ε) > 0` is one. -/
theorem lemma_3_2 {m : ℕ} (v : Finset (Fin m) → ℝ)
    (hv : IsNormalized v ∧ IsMonotone v ∧ IsSubadditive v) (S : Finset (Fin m))
    (hS : S.Nonempty) (hV : 0 < v S) (π : Fin m → ℝ) (hπ : ∀ j ∈ S, 0 ≤ π j)
    (ρ ε δ : ℝ) (hρ : 1 < ρ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 ≤ δ)
    (τ : ℕ) (hτ : Real.logb ρ ((S.card : ℝ) / ε) ≤ τ) (p : ℕ → ℝ)
    (hp : ∀ t ≤ τ, ε * v S / S.card * ρ ^ t ≤ p t ∧ p t ≤ ε * v S / S.card * ρ ^ t + δ) :
    (1 - ε) * v S - ρ * ∑ j ∈ S, π j - 2 * (S.card : ℝ) * δ ≤
      ∑ t ∈ Finset.range (τ + 1), singlePriceProfit v S π (p t) := by sorry

end DraftPoA
