-- Prove2me | Theorems.Thm_CEPolytopeHard_Supplement_theorem_2
-- name    : CEPolytopeHard.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:14:10.706922+00:00
-- url     : https://prove2.me/theorems/dfd23e91-12a2-4854-b1cf-aa3a82ad2de9
-- title:
--   Theorem 2 — computing a $d^{-c}$-correlated equilibrium with at most $d^C$ profiles is PPAD-hard in two-player quadratic concave games on $[0,1]^d$
-- statement:
--   Consider two-player games with strategy sets $X_1=X_2=[0,1]^d$ whose utilities $u_1,u_2:[0,1]^d\times[0,1]^d\to[0,1]$ are given by arithmetic circuits and are **quadratic concave in the player's own strategy**: for every fixed opponent strategy $x_{-i}$,
--   $$u_i(x_i,x_{-i})=c_i(x_{-i})+b_i(x_{-i})^\top x_i-x_i^\top A_i(x_{-i})x_i,\qquad A_i(x_{-i})\succeq0 .$$
--   A finite-support distribution $\mu$ on profiles is an **$\epsilon$-correlated equilibrium** if for each player $i$ and every map $\phi:[0,1]^d\to[0,1]^d$,
--   $$\mathbb E_{x\sim\mu}\big[u_i(\phi(x_i),x_{-i})-u_i(x)\big]\le\epsilon .$$
--
--   **Theorem 2.** For every fixed $C\ge1$ there is a constant $c>0$ such that computing a $d^{-c}$-correlated equilibrium supported on at most $d^{C}$ strategy profiles is PPAD-hard, even in these two-player concave games on $[0,1]^d$ whose utilities are quadratic in the player's own strategy.
--
--   Thus computing a correlated equilibrium with polynomial support in such games is as hard as computing a Nash equilibrium, in contrast with normal-form games, where correlated equilibria are computable by linear programming.
--
--   **Formalization Note** The problem is `quadCEProblem C c`; PPAD-hardness is the mission's `PPADHard`. Utilities are continuous on the strategy space (the standing convention of concave games).
--
--   Differences from the source:
--   - encoding: PPAD-hard (not defined in the paper) → PPADHard (the mission's published definition); reason: standard Levin search reductions on Cook's machines, as in the base mission
--   - reading: two-player concave game on X_1 = X_2 = [0,1]^d (Turing model, Section 2.1: functions given as arithmetic circuits with standard gates) → two valid well-behaved NadlerCLS.Circ utilities with 2d inputs and one output, code encNat d ++ encCirc U₁ ++ encCirc U₂, d ≥ 1; reason: Section 2.1's representation of functions, read as well-behaved (polynomial-time evaluable) circuits, which narrows the instance class; d = 0 is the empty degenerate case
--   - reading: "each utility is quadratic in the player’s own strategy" (Section 2.3: u_i = b_i(x_{−i})ᵀx_i − x_iᵀA_i(x_{−i})x_i, A_i : X_{−i} → S^d_+) → on the box, u_i = c_i(x_{−i}) + b_i(x_{−i})ᵀx_i − x_iᵀA_i(x_{−i})x_i with A_i symmetric PSD (QuadGame.Valid); reason: the words say "a quadratic concave function in x_i"; the paper's own imitation game (Proposition 3.6) has an opponent-only term; such a term changes no deviation gain
--   - reading: concave game utilities u_i : X → [0,1] (Section 2.3) → values in [0,1] on [0,1]^d × [0,1]^d are part of the validity of an instance; reason: a promise on instances (Section 2.1); without it the accuracy d^{−c} could be rescaled away
--   - reading: concave games (Section 2.3; continuity not written) → utilities continuous on [0,1]^d × [0,1]^d (QuadGame.Valid); reason: standing convention of concave games, satisfied by the paper's games; a discontinuous instance may have no ε-CE, which would let a reduction map to answerless instances; the restriction narrows the instance class, so the hardness claim is not weakened
--   - encoding: a d^{−c}-correlated equilibrium supported on at most d^C strategy profiles, listed by support and probabilities (Section 2.1) → a list of (rational weight ≥ 0, rational profile [x, y]) with Σ w = 1, equal profiles merged, IsApproxCE with all maps [0,1]^d → [0,1]^d at accuracy (d:ℝ)^(−c), support card ≤ (d:ℝ)^C; reason: Section 2.1's output form and Section 2.3's swap deviations
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 2, p.5 (follows from Theorem 1 and Proposition 3.6, p.14)

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_CEPolytopeHard_Supplement_quadCEProblem

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

/-- **Theorem 2** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of
Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2,
2026, sha256 6aec500a…7820, Theorem 2, p.5): "For every fixed C ≥ 1, there is a constant c > 0
such that computing a d^{−c}-correlated equilibrium supported on at most d^C strategy profiles is
PPAD-hard, even in two-player concave games with X_1 = X_2 = [0, 1]^d where each utility is
quadratic in the player’s own strategy."

**Formalization Note** The game class is `quadCEProblem C c`: utilities given by arithmetic
circuits (Section 2.1), with values in `[0,1]` (Section 2.3), concave quadratic in the own
strategy, continuous on the strategy space (the standing convention of concave games). An
additive term depending only on the opponent is allowed (it does not change any deviation gain).
Correlated equilibria allow every deviation map `[0,1]^d → [0,1]^d`. -/
theorem theorem_2 :
    ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧ PPADHard (quadCEProblem C c) := by sorry

end CEPolytopeHard.Supplement
