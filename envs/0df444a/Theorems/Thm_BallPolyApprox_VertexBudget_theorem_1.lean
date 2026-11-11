-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_theorem_1
-- name    : BallPolyApprox.VertexBudget.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:54:37.053819+00:00
-- url     : https://prove2.me/theorems/8eb00d28-21b1-409b-a32f-ca12b2feff07
-- title:
--   Theorem 1 — the minimum vertex budget satisfies $\log N_\varepsilon(d)\asymp d\log(1+1/(\varepsilon\sqrt d))$, with (4) and $N_\varepsilon(d)=\exp(\Theta_\varepsilon(\sqrt d))$
-- statement:
--   Let $N_\varepsilon(d)=\min\{N\in\mathbb N:\exists P\in\mathcal P_d(N)\text{ with }\Delta_d(P)\le\varepsilon\}$, where $\mathcal P_d(N)$ is the class of polytopes in $\mathbb R^d$ in unrestricted position with at most $N$ vertices and $\Delta_d(P)=|B_d\triangle P|/|B_d|$. There are absolute constants $c,C>0$, $d_0\ge3$ and $\varepsilon_0\in(0,1)$ such that for all $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$,
--   $$cd\log\Big(1+\frac1{\varepsilon\sqrt d}\Big)\le\log N_\varepsilon(d)\le Cd\log\Big(1+\frac1{\varepsilon\sqrt d}\Big)\quad(3).$$
--   The upper bound holds for every $0<\varepsilon<1$ and is attained by an origin-symmetric polytope. Moreover, for every $0<\varepsilon<1$ and every $d\ge\max\{d_0,4\log\frac8{1-\varepsilon}\}$,
--   $$\log N_\varepsilon(d)\ge\frac{c\sqrt d}{\log(8/(1-\varepsilon))}-\log\frac8{3(1-\varepsilon)}\quad(4).$$
--   In particular, for each fixed $0<\varepsilon<1$, $N_\varepsilon(d)=\exp(\Theta_\varepsilon(\sqrt d))$ as $d\to\infty$.
--
--   Logarithms are natural; one choice of $c,C,d_0,\varepsilon_0$ serves all four clauses.
--
--   Differences from the source:
--   - encoding: bounds on log N_ε(d), N_ε(d) = min{N : ∃ P ∈ P_d(N), Δ_d(P) ≤ ε} → a lower bound X ≤ log N_ε(d) as: every finite V with Δ_d(conv V) ≤ ε has X ≤ log|V|; an upper bound log N_ε(d) ≤ Y as: some finite V with Δ_d(conv V) ≤ ε has log|V| ≤ Y; reason: equivalent since N_ε(d) is the least |V|; avoids sInf ∅ = 0 making the upper bound vacuous
--   - encoding: upper bound of (3) for 0 < ε ≤ ε_0, and separately for every 0 < ε < 1 attained by an origin-symmetric polytope → one clause for every 0 < ε < 1 and d ≥ d_0 with an origin-symmetric V (V = −V); reason: the all-ε clause contains the ε ≤ ε_0 case with the same C
--   - encoding: N_ε(d) = exp(Θ_ε(√d)) as d → ∞ → for each ε ∈ (0, 1): ∃ a, b > 0, ∃ D, ∀ d ≥ D, some V with Δ_d ≤ ε has log|V| ≤ b√d, and every V with Δ_d ≤ ε has a√d ≤ log|V|; reason: the definition of Θ_ε(√d) for log N_ε(d), in the same existence/for-all encoding
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Theorem 1, p. 3 (PDF 5)

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError

set_option autoImplicit false

namespace BallPolyApprox.VertexBudget

/-- Theorem 1 (p. 3, PDF 5). There are absolute constants `c, C > 0`, `d_0 ≥ 3` and
`ε_0 ∈ (0, 1)` such that, with `N_ε(d)` the least number of vertices of a polytope `P ⊂ ℝ^d`
(vertices anywhere) with `Δ_d(P) ≤ ε`:
* (3), lower: `c d log(1 + 1/(ε√d)) ≤ log N_ε(d)` for `d ≥ d_0`, `0 < ε ≤ ε_0`;
* (3), upper, for every `0 < ε < 1` and attained by an origin-symmetric polytope:
  `log N_ε(d) ≤ C d log(1 + 1/(ε√d))` for `d ≥ d_0`;
* (4): `log N_ε(d) ≥ c√d / log(8/(1−ε)) − log(8/(3(1−ε)))` for every `0 < ε < 1` and every
  `d ≥ max{d_0, 4 log(8/(1−ε))}`;
* for each fixed `0 < ε < 1`, `N_ε(d) = exp(Θ_ε(√d))` as `d → ∞`.
A lower bound on `log N_ε(d)` is stated for every finite vertex set `V` whose hull has
`Δ_d ≤ ε`; an upper bound is the existence of such a `V`. -/
theorem theorem_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d0 : ℕ, 3 ≤ d0 ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < 1 ∧
      (∀ d : ℕ, d0 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ V : Finset (Rd d),
        ballErr (polytope V) ≤ ε →
          c * d * Real.log (1 + 1 / (ε * Real.sqrt d)) ≤ Real.log V.card) ∧
      (∀ d : ℕ, d0 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ V : Finset (Rd d), IsOriginSymmetric V ∧ ballErr (polytope V) ≤ ε ∧
          Real.log V.card ≤ C * d * Real.log (1 + 1 / (ε * Real.sqrt d))) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ d : ℕ, d0 ≤ d → 4 * Real.log (8 / (1 - ε)) ≤ (d : ℝ) →
        ∀ V : Finset (Rd d), ballErr (polytope V) ≤ ε →
          c * Real.sqrt d / Real.log (8 / (1 - ε)) - Real.log (8 / (3 * (1 - ε))) ≤
            Real.log V.card) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
        (∃ V : Finset (Rd d), ballErr (polytope V) ≤ ε ∧ Real.log V.card ≤ b * Real.sqrt d) ∧
        (∀ V : Finset (Rd d), ballErr (polytope V) ≤ ε → a * Real.sqrt d ≤ Real.log V.card)) := by sorry

end BallPolyApprox.VertexBudget
