-- Prove2me | Theorems.Thm_CEPolytopeHard_theorem_4
-- name    : CEPolytopeHard.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:49.787357+00:00
-- url     : https://prove2.me/theorems/fa09b2c2-0f10-4712-9dc5-c8967cb672e2
-- title:
--   Theorem 4 — computing an approximate correlated equilibrium with polynomial support in a multilinear polytope game is PPAD-hard
-- statement:
--   Let $N$ be the binary encoding length of a multilinear polytope game (explicit rational inequalities for each player's polytope, explicit rational monomials for each utility, utilities in $[0,1]$ on the profile set). For a number of players $n_0$, a real $C \ge 1$ and an accuracy $\varepsilon(N)$, consider the problem: given an $n_0$-player game, output an $\varepsilon(N)$-correlated equilibrium supported on at most $N^C$ profiles. Then:
--
--   1. **(exponential accuracy)** there is an absolute constant $n_0$ such that for every $C \ge 1$ there is $k \in \mathbb N$ for which the problem at accuracy
--   $$
--   \varepsilon(N) = 2^{-(N^k + k)}
--   $$
--   is PPAD-hard;
--   2. **(polynomial accuracy, conditional)** if Assumption 2.2 (PCP-for-PPAD) holds, there is an absolute constant $n_0$ such that for every $C \ge 1$ there is $c > 0$ for which the problem at accuracy
--   $$
--   \varepsilon(N) = N^{-c}
--   $$
--   is PPAD-hard.
--
--   So correlated equilibria, which are computable by linear programming in normal-form games, become PPAD-hard as soon as strategy sets are polytopes, for every prescribed polynomial support bound and already with a constant number of players.
--
--   Differences from the source:
--   - encoding: PPAD-hard (not defined in the paper) → PPADHard: every problem of the public QuasiStrictNE.PPAD reduces by CardinalMatching.SearchReduces; reason: standard Levin reductions on Cook's machines
--   - reading: accuracy ϵ = 2^{−poly(N)} → ∃ k ∈ ℕ with ε(N) = 2^{−(N^k + k)}, after ∀ C; reason: every polynomial is dominated by some N^k + k on ℕ, and a smaller accuracy has fewer answers, so this is "for some polynomial"
--   - reading: "Both statements hold even when the number of players is an absolute constant" → ∃ n₀ before ∀ C, instances with exactly n₀ players (one n₀ per clause); reason: the proof uses q + 2 = 2p + 3 players with p depending only on τ; ∀ C ∃ n₀ or "at most n₀" would be weaker
--   - reading: utilities u_i : X → [0, 1] (Section 2.3) → the range [0, 1] on X is part of the validity of an instance; reason: a promise on instances, as in Section 2.1; without it the accuracy could be rescaled away
--   - encoding: multilinear game on explicit rational polytopes, binary encoding length N → MLGame with well-formedness (players in a monomial pairwise distinct), nonempty bounded polytopes; N = length of MLGame.encode; reason: Lean representation of Section 2.3's game class and its encoding
--   - encoding: an ϵ-correlated equilibrium supported on at most N^C profiles, output as a list of support points and probabilities → a list of (rational weight ≥ 0, rational profile) pairs with Σ w = 1, equal profiles merged, IsApproxCE with all maps X_i → X_i, at most N^C distinct profiles of positive weight (real power); reason: Section 2.1's output form and Section 2.3's swap deviations; no length bound on answers
--   - reading: Assumption 2.2's generalized circuits → the Section 2.5 class with fan-out two (GCircuit, gcircuitProblem); reason: Assumption 2.2 refers to the Section 2.5 definition
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 4, p.6 (restated p.19); proof pp.19–25

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_CEPolytopeHard_ceProblem
import Definitions.Def_CEPolytopeHard_Assumption_2_2

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Theorem 4 (correlated equilibria with polynomial support in multilinear polytope games are
PPAD-hard)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Theorem 4, p.6, restated p.19: "Let N be the binary encoding length of the
game’s description. For every fixed C ≥ 1, computing an ϵ-correlated equilibrium supported on at
most N^C profiles in a multilinear game on explicit rational polytopes is (i) PPAD-hard at accuracy
ϵ = 2^{−poly(N)}; (ii) PPAD-hard at accuracy ϵ = N^{−c} for some constant c > 0, assuming the
PCP-for-PPAD conjecture (Assumption 2.2). Both statements hold even when the number of players is
an absolute constant").

1. There is a number of players `n₀` such that for every real `C ≥ 1` there is `k ∈ ℕ` for which
   computing a `2^{−(N^k + k)}`-correlated equilibrium with at most `N^C` support profiles in an
   `n₀`-player multilinear polytope game of encoding length `N` is PPAD-hard.
2. If Assumption 2.2 holds, there is `n₀` such that for every real `C ≥ 1` there is `c > 0` for
   which the same problem at accuracy `N^{−c}` is PPAD-hard.

**Formalization Note** `2^{−poly(N)}` is `2^{−(N^k + k)}` for some `k` (every polynomial is
dominated by some `N^k + k`, and a smaller accuracy has fewer answers). "The number of players is
an absolute constant" is `∃ n₀` before `∀ C`, with instances of exactly `n₀` players. Validity of an
instance includes utilities in `[0, 1]` and nonempty bounded polytopes (Section 2.3, p.11).
PPAD-hardness is `PPADHard` (reductions from every problem of the public `QuasiStrictNE.PPAD`). -/
theorem theorem_4 :
    (∃ n₀ : ℕ, ∀ C : ℝ, 1 ≤ C → ∃ k : ℕ,
      PPADHard (ceProblem n₀ C (fun N => ((2 : ℝ) ^ (N ^ k + k))⁻¹))) ∧
    (Assumption_2_2 → ∃ n₀ : ℕ, ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧
      PPADHard (ceProblem n₀ C (fun N => (N : ℝ) ^ (-c)))) := by sorry

end CEPolytopeHard
