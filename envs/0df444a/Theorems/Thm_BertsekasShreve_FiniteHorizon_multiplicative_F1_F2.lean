-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_multiplicative_F1_F2
-- name    : BertsekasShreve.FiniteHorizon.multiplicative_F1_F2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:29.331802+00:00
-- url     : https://prove2.me/theorems/74738ca9-24b6-466c-9d1e-286df0b031c5
-- title:
--   Proposition 3.6 — the multiplicative-cost mapping (33) satisfies F.1, and F.2 with α = b when 0 ≤ g ≤ b
-- statement:
--   Let $(S,C,U,H)$ be a model whose mapping is the multiplicative-cost mapping of Section 2.3.4,
--   $$H(x,u,J)=E\{g(x,u,w)J[f(x,u,w)]\mid x,u\},$$
--   where $w$ ranges over a countable set $W$ with probability distribution $p(\cdot\mid x,u)$, $f$ maps into $S$, $g$ maps into $R^*$, and $g(x,u,w)\ge0$ for all $x\in S$, $u\in U(x)$, $w\in W$. Then:
--
--   1. $H$ satisfies Assumption F.1;
--   2. if there is $b\in R$ with $0\le g(x,u,w)\le b$ for all $x\in S$, $u\in U(x)$, $w\in W$, then $H$ satisfies Assumption F.2, and the inequality of F.2 holds with $\alpha=b$:
--   $$H(x,u,J)\le H(x,u,J+r)\le H(x,u,J)+br\qquad(r>0,\ J\in F,\ x\in S,\ u\in U(x)).$$
--
--   Together with Proposition 3.1 this yields the DP algorithm for the multiplicative (e.g. exponential) cost criterion.
--
--   **Formalization Note** The expectation uses the book's convention $\infty-\infty=\infty$; $p(\cdot\mid x,u)$ is a `PMF W` with `[Countable W]`. The second conclusion is stated as both "F.2 holds" and "the F.2 inequality holds with constant $b$", because $b=0$ is allowed by the hypothesis while F.2 asks for a constant in $(0,\infty)$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 50, Proposition 3.6, eq. (33) of Chapter 3; model of Section 2.3.4, p. 37, eqs. (26)–(27) of Chapter 2; expectation of Section 2.3.2, p. 31

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.6 (Bertsekas & Shreve 1996, p. 50). Let `m` be a model whose mapping is the
multiplicative-cost mapping `H(x, u, J) = E{g(x, u, w) J[f(x, u, w)] | x, u}` of Section 2.3.4
(eq. (33) of Chapter 3), with `w` in a countable set `W` distributed according to
`p(· | x, u)`, and `g(x, u, w) ≥ 0` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W` (eq. (27) of
Chapter 2). Then `H` satisfies F.1. If there is `b ∈ R` with `0 ≤ g(x, u, w) ≤ b` for all
`x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then `H` satisfies F.2, with the inequality of F.2 holding for
the constant `α = b`. -/
theorem multiplicative_F1_F2 {S C W : Type*} [Countable W] (m : Model S C)
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S)
    (hg : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w)
    (hH : m.H = multiplicativeH p g f) :
    m.AssumptionF1 ∧
    ∀ b : ℝ, (∀ x, ∀ u ∈ m.U x, ∀ w, g x u w ≤ (b : EReal)) →
      m.AssumptionF2 ∧ m.F2With b := by sorry

end BertsekasShreve.FiniteHorizon
