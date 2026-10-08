-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_minimax_F2
-- name    : BertsekasShreve.FiniteHorizon.minimax_F2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:19.524154+00:00
-- url     : https://prove2.me/theorems/2c9ae67e-071b-4c54-a6cb-ab4eb105144d
-- title:
--   Proposition 3.7 — the minimax mapping (34) satisfies F.2 with constant α
-- statement:
--   Let $(S,C,U,H)$ be a model whose mapping is the minimax mapping of Section 2.3.5,
--   $$H(x,u,J)=\sup_{w\in W(x,u)}\{g(x,u,w)+\alpha J[f(x,u,w)]\},$$
--   where $W(x,u)\subseteq W$ is nonempty for every $x\in S$, $u\in U(x)$, $g$ maps into $[-\infty,\infty]$, $f$ maps into $S$, the scalar $\alpha$ is positive, and the sum uses the convention $\infty-\infty=\infty$. Then $H$ satisfies Assumption F.2 with the constant $\alpha$: for every $r>0$, $J\in F$, $x\in S$, $u\in U(x)$,
--   $$H(x,u,J)\le H(x,u,J+r)\le H(x,u,J)+\alpha r.$$
--
--   Combined with Proposition 3.1(b), this gives the DP algorithm and $\varepsilon$-optimal policies for finite-horizon minimax control.
--
--   **Formalization Note** The hypothesis `m.H = minimaxH Wset g f α` identifies the model's mapping; the Monotonicity Assumption is part of the model and holds for this mapping. The conclusion `F2With m α` names the book's constant; since $\alpha>0$ it is Assumption F.2.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 51, Proposition 3.7, eq. (34) of Chapter 3; model of Section 2.3.5, p. 38

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.7 (Bertsekas & Shreve 1996, p. 51). Let `m` be a model whose mapping is the
minimax mapping `H(x, u, J) = sup_{w ∈ W(x,u)} {g(x, u, w) + α J[f(x, u, w)]}` of Section 2.3.5
(eq. (34) of Chapter 3), where `W(x, u)` is nonempty for `x ∈ S`, `u ∈ U(x)`, `g` maps into
`[−∞, ∞]`, `f` into `S`, and the scalar `α` is positive. Then `H` satisfies F.2, with the
inequality of F.2 holding for the same constant `α`. -/
theorem minimax_F2 {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hW : ∀ x, ∀ u ∈ m.U x, (Wset x u).Nonempty)
    (hH : m.H = minimaxH Wset g f α) :
    m.F2With α := by sorry

end BertsekasShreve.FiniteHorizon
