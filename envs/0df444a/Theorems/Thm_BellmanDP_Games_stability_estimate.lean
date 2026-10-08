-- Prove2me | Theorems.Thm_BellmanDP_Games_stability_estimate
-- name    : BellmanDP.Games.stability_estimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:16:51.767548+00:00
-- url     : https://prove2.me/theorems/e18054e0-4d02-45d0-b3cb-b427a08a546f
-- title:
--   Chapter X, Theorem 4 — stability: $|f-F|\le\sum_{n\ge0}\Delta(k^nc)$
-- statement:
--   Let two multi-stage games share all their data except the single-stage return, $R$ in the first and $R'$ in the second, and let both satisfy the hypotheses of Theorem 1 of Chapter X with the same constant $k$. Let $f$ and $F$ be the solutions of
--   $$f(P,P')=\max_G\min_{G'}\iint\big[R(u,v)+h(P,P';u,v)f(T,T')\big]\,dG\,dG'=\min_{G'}\max_G[\ \cdots\ ],$$
--   $$F(P,P')=\max_G\min_{G'}\iint\big[R'(u,v)+h(P,P';u,v)F(T,T')\big]\,dG\,dG'=\min_{G'}\max_G[\ \cdots\ ]$$
--   in the class of Theorem 1. With
--   $$\Delta(c)=\max_{\|P\|+\|P'\|\le c}\ \max_{u\in S,\,v\in S'}|R(u,v)-R'(u,v)|,$$
--   the solutions satisfy, for $\|P\|+\|P'\|\le c$,
--   $$|f(P,P')-F(P,P')|\le\sum_{n=0}^{\infty}\Delta(k^nc).$$
--
--   The estimate shows that the solution depends continuously on the single-stage return.
--
--   **Formalization Note** The maximum $\Delta$ is replaced by an arbitrary majorant $\Delta'$ of $|R-R'|$ on the regions $\|P\|+\|P'\|\le c$ for which $\sum_n\Delta'(k^nc)$ converges. The book's $\Delta$ is such a majorant, and a bound for every majorant is equivalent to the bound for $\Delta$. The book leaves $c$ unspecified; it is any $c\ge\|P\|+\|P'\|$. Bellman prints the min-max of the first equation with the subscripts $G$, $G'$ interchanged (p. 301); the equation used is that of Theorem 1.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 16, Theorem 4, pp. 301-302

import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 4, pp. 301–302 (stability). Let the games `g`
(return `R`) and `g'` (the same data with return `R'`) both satisfy the hypotheses of Theorem 1
with the same `k`, and let `f`, `F` be the solutions of the corresponding equations (16.2) in the
class of Theorem 1. With
`Δ(c) = Max_{‖P‖ + ‖P'‖ ≤ c} Max_{u ∈ S, v ∈ S'} |R(u, v) − R'(u, v)|`,
`|f(P, P') − F(P, P')| ≤ Σ_{n=0}^∞ Δ(kⁿ c)` for `c ≥ ‖P‖ + ‖P'‖`. The maximum `Δ` is expressed
through a majorant: the bound holds for every `Δ'` dominating `|R − R'|` on the regions
`‖P‖ + ‖P'‖ ≤ c` with `Σ_n Δ'(kⁿ c)` convergent. -/
theorem stability_estimate {n n' m m' : ℕ} (g : GameData n n' m m') (R' : Vec m → Vec m' → ℝ)
    (k : ℝ) (hg : GameHyp g k) (hg' : GameHyp { g with R := R' } k)
    (f F : Vec n → Vec n' → ℝ) (hf : InSolutionClass g f) (hfs : IsGameSolution g f)
    (hF : InSolutionClass { g with R := R' } F) (hFs : IsGameSolution { g with R := R' } F)
    (Δ : ℝ → ℝ)
    (hΔ : ∀ c : ℝ, ∀ P ∈ g.D, ∀ P' ∈ g.D', l1norm P + l1norm P' ≤ c →
      ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')), |g.R u v - R' u v| ≤ Δ c)
    (P : Vec n) (hP : P ∈ g.D) (P' : Vec n') (hP' : P' ∈ g.D') (c : ℝ)
    (hc : l1norm P + l1norm P' ≤ c) (hsum : Summable (fun j : ℕ => Δ (k ^ j * c))) :
    |f P P' - F P P'| ≤ ∑' j : ℕ, Δ (k ^ j * c) := by sorry

end BellmanDP.Games
