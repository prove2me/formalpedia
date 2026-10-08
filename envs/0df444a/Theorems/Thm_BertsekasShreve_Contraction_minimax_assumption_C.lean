-- Prove2me | Theorems.Thm_BertsekasShreve_Contraction_minimax_assumption_C
-- name    : BertsekasShreve.Contraction.minimax_assumption_C
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:14:49.377677+00:00
-- url     : https://prove2.me/theorems/71c8e8bf-f3eb-40bc-acfd-4f11bffd3f7d
-- title:
--   Proposition 4.11 — the discounted minimax model with bounded nonnegative cost satisfies Assumption C with $\bar B=B$, $m=1$
-- statement:
--   Consider the minimax control model of Section 2.3.5: $w$ takes values in a set $W$, and $W(x,u)$ is a nonempty subset of $W$ for each $x\in S$, $u\in U(x)$; $g:S\times C\times W\to[-\infty,\infty]$ and $f:S\times C\times W\to S$; $\alpha>0$; and
--
--   $$H(x,u,J)=\sup_{w\in W(x,u)}\bigl\{g(x,u,w)+\alpha J[f(x,u,w)]\bigr\},\qquad J_0(x)=0\quad\forall x\in S.$$
--
--   Assume $\alpha<1$ and that for some $b\in\mathbb R$
--
--   $$0\le g(x,u,w)\le b\qquad\forall x\in S,\ u\in U(x),\ w\in W.$$
--
--   Then Assumption C is satisfied with $\bar B=B$, $m=1$, and the scalars in (2) and (3) both equal to $\alpha$ (that is, $\rho=\alpha$).
--
--   The proposition places discounted minimax control, and with it sequential zero-sum games against nature, inside the contraction framework, so that Propositions 4.1–4.5 apply to it.
--
--   **Formalization Note** The model is any `Model` whose `H` is given by (34) and whose `J0` is $0$; the sum $g+\alpha J$ is computed in `EReal`, where it never involves opposite infinities since $g$ is finite on the relevant arguments.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 69, Proposition 4.11, Eq. (34) of Chapter 4; p. 38, Section 2.3.5, Eq. (29) of Chapter 2 and assumptions (1)–(3)

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.11, p. 69. The minimax model of Section 2.3.5 (p. 38):
`H(x, u, J) = sup_{w ∈ W(x,u)} {g(x, u, w) + α J[f(x, u, w)]}` (eq. (34)), with `W(x, u)` a nonempty
subset of `W` for `x ∈ S`, `u ∈ U(x)`, `f : SCW → S`, `g : SCW → R*`, `α > 0`, and `J₀ = 0`.
If `α < 1` and `0 ≤ g(x, u, w) ≤ b` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then Assumption C holds
with `B̄ = B`, `m = 1`, and the scalars in (2) and (3) both equal to `α`. -/
theorem minimax_assumption_C {S C W : Type*} (P : Model S C) (Wset : S → C → Set W)
    (hW : ∀ x, ∀ u ∈ P.U x, (Wset x u).Nonempty) (g : S → C → W → EReal) (f : S → C → W → S)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hH : ∀ (x : S) (u : C) (J : S → EReal),
      P.H x u J = ⨆ w ∈ Wset x u, (g x u w + (α : EReal) * J (f x u w)))
    (hJ0 : P.J0 = fun _ => 0) (b : ℝ)
    (hg : ∀ x, ∀ u ∈ P.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ (b : EReal)) :
    AssumptionC P Set.univ 1 α α := by sorry

end BertsekasShreve.Contraction
