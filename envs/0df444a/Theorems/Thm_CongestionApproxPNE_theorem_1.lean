-- Prove2me | Theorems.Thm_CongestionApproxPNE_theorem_1
-- name    : CongestionApproxPNE.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:51.195345+00:00
-- url     : https://prove2.me/theorems/dc1f3848-e9d6-498c-ba8c-e341214bdf86
-- title:
--   Theorem 1 — polynomial congestion games of degree $d$ with no $\alpha$-PNE for $\alpha<\alpha(d)$, and $\alpha(d)\ge\sqrt d/(2\ln d)$ for large $d$
-- statement:
--   For an integer $d$, let
--
--   $$
--   \alpha(d)=\sup_{n,k,w,\beta}\ \min\left\{\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta},\ \frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}\right\}
--   \quad\text{s.t. } n\in\mathbb N,\ k\in\{1,\dots,d\},\ w\in[0,1],\ \beta\in[0,1]. \tag{3}
--   $$
--
--   Then:
--
--   1. for every integer $d\ge 2$ there is a weighted polynomial congestion game of degree $d$ that has no $\alpha$-approximate pure Nash equilibrium for any $\alpha$ with $1\le\alpha<\alpha(d)$;
--   2. $\alpha(d)=\Omega\!\left(\frac{\sqrt d}{\ln d}\right)$ as $d\to\infty$;
--   3. $\alpha(d)\ge\frac{\sqrt d}{2\ln d}$ for all sufficiently large $d$.
--
--   It is the first super-constant lower bound on the factor $\alpha$ for which every weighted polynomial congestion game of degree $d$ has an $\alpha$-PNE: before it, $d$-PNE were known to exist while nonexistence was known only for $1.153$-PNE (abstract, p.1).
--
--   **Formalization Note** A game is `HarksKlimm.Consistency.Game N M` (finitely many and at least one player and resource, nonempty strategy sets, positive weights); "polynomial of degree $d$" is `IsPolyGame d`; $\alpha(d)$ is `alphaBound d`, the exact supremum (3); clause 2 is `(fun d => √d / ln d) =O[atTop] alphaBound`.
--
--   Differences from the source:
--   - reading: "there exist (weighted) polynomial congestion games of degree d that do not have α-PNE for any α < α(d)" → one game G with no α-PNE for every α ∈ [1, α(d)) (∃ G, ∀ α); reason: of the readings "for each α some game" and "one game for all α", the second is stronger; it holds because the supremum (3) is attained when α(d) > 1
--   - encoding: α-PNE for α ≥ 1; "for any α < α(d)" → 1 ≤ α as a hypothesis, α-PNE predicate without the α ≥ 1 requirement; reason: the paper defines α-PNE only for α ≥ 1
--   - encoding: α(d) = sup over n ∈ ℕ, k ∈ {1,…,d}, w, β ∈ [0, 1] of the min of the two ratios (3) → sSup of the min over those points at which the second denominator (nw)^k + β(1+w)^d is positive; reason: (3) is undefined where that denominator is 0 (nw = 0, β = 0); with the convention 1/0 = +∞ those points give the value 1, already in the set, so the supremum is unchanged; the set is nonempty and bounded by 2^d
--   - encoding: polynomial cost functions c_e : ℝ>0 → ℝ≥0 → cost agrees with a polynomial at every load x ≥ 0 (x : ℝ≥0); reason: the load of a resource in a player's strategy is at least her positive weight, so the value at 0 never enters a cost; requiring it only narrows the class of games
--   - encoding: α(d) = Ω(√d/ln d) → (fun d => √d / ln d) =O[atTop] (fun d => α(d)) over d : ℕ; reason: Big-Omega is the reversed Big-O; α(d) ≥ 1 > 0, so absolute values change nothing
--   - encoding: a congestion game with finite nonempty sets N of players and E of resources, nondecreasing costs c_e : ℝ>0 → ℝ≥0, weights w_i > 0 and strategy sets S_i ⊆ 2^E → HarksKlimm.Consistency.Game N M (players Fin N, resources Fin M, 0 < N, 0 < M, nonempty strategy Finsets, positive ℝ≥0 weights, cost : Fin M → ℝ≥0 → ℝ); reason: finite sets are indexed by Fin; nondecreasing and nonnegative costs follow from IsPolyGame's nonnegative coefficients; nonempty strategy sets only narrow the class of games in the existential (an empty S_i leaves no profile at all)
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Theorem 1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_CongestionApproxPNE_IsApproxPNE
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_CongestionApproxPNE_alphaBound

set_option autoImplicit false
open scoped NNReal

open Filter

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **Theorem 1: weighted polynomial congestion games of degree `d` with no α-PNE for any
`α < α(d)`, and `α(d) = Ω(√d/ln d)`, `α(d) ≥ √d/(2 ln d)` for large `d`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, Theorem 1, p.4: "For any integer d ≥ 2, there exist (weighted) polynomial congestion games
of degree d that do not have α-PNE for any α < α(d), where α(d) = sup_{n,k,w,β} min{…} (3) s.t.
n ∈ N, k ∈ {1, . . . , d}, w ∈ [0, 1], β ∈ [0, 1]. In particular, we have the asymptotics
α(d) = Ω(√d/ln d) and the bound α(d) ≥ √d/(2 ln d), valid for large enough d."

1. For every integer `d ≥ 2` there is one weighted polynomial congestion game of degree `d` that
   has no α-PNE for any `α` with `1 ≤ α < α(d)`.
2. `√d / ln d = O(α(d))` as `d → ∞`, i.e. `α(d) = Ω(√d/ln d)`.
3. There is `d₀` with `α(d) ≥ √d/(2 ln d)` for every integer `d ≥ d₀`.

**Formalization Note** Clause 1 takes the reading "one game for every `α < α(d)`" (stronger than
"for each `α` some game"). The game is `HarksKlimm.Consistency.Game N M` (finitely many, at least
one, players and resources; nonempty strategy sets; positive weights); `IsPolyGame d` asks for
cost polynomials of degree `≤ d` with nonnegative coefficients. `α(d)` is `alphaBound d`, the
exact supremum (3). α-PNE is defined for `α ≥ 1` (p.3), hence the range `1 ≤ α`. -/
theorem theorem_1 :
    (∀ d : ℕ, 2 ≤ d → ∃ (N M : ℕ) (G : Game N M), IsPolyGame d G ∧
      ∀ α : ℝ, 1 ≤ α → α < alphaBound d → ∀ s : G.Profile, ¬ IsApproxPNE G α s) ∧
    (fun d : ℕ => Real.sqrt d / Real.log d) =O[atTop] (fun d : ℕ => alphaBound d) ∧
    (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → Real.sqrt d / (2 * Real.log d) ≤ alphaBound d) := by sorry

end CongestionApproxPNE
