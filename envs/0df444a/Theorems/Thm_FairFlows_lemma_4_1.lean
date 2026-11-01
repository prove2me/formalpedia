-- Prove2me | Theorems.Thm_FairFlows_lemma_4_1
-- name    : FairFlows.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:16.329854+00:00
-- url     : https://prove2.me/theorems/3a07d6e3-ba2c-4cdc-a795-870c0cb2fce8
-- title:
--   Lemma 4.1 — saturated edges cover $p$; covers give $(f,g^-+\chi_X)$-bounded flows
-- statement:
--   Let $D=(V,A)$, $m:V\to\mathbb Z$ with $\widetilde m(V)=0$, bounds $f\le g$, and $L\subseteq A$ with $-\infty<f(e)<g(e)<+\infty$ for every $e\in L$. Let $g^-=g-\chi_L$ and $p=\widetilde m-\varrho_{g^-}+\delta_f$ (4.2).
--
--   1. (A) If $x$ is an integer-valued $(f,g)$-bounded $m$-flow, then the set $X=\{e\in L: x(e)=g(e)\}$ of its $g$-saturated $L$-edges covers $p$.
--   2. (B) If a subset $X\subseteq L$ covers $p$, then there is an integer-valued $(f,g^-+\chi_X)$-bounded $m$-flow.
--
--   Part (B) is where Hoffman's integral feasibility theorem enters the proof of Theorem 2.1.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Lemma 4.1, p.10 (§4 setting p.10)

import Mathlib
import Definitions.Def_FairFlows_UpperMin

set_option autoImplicit false

namespace FairFlows

/-- Lemma 4.1 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.10). In the setting of §4 (`m̃(V) = 0`, `f ≤ g`,
`−∞ < f(e) < g(e) < +∞` on `L`), with `p = m̃ − ϱ_{g⁻} + δ_f` (4.2) and `g⁻ = g − χ_L` (4.1):
(A) if `x` is an integer-valued `(f, g)`-bounded `m`-flow, then its set
`X = {e ∈ L : x(e) = g(e)}` of `g`-saturated `L`-edges covers `p`; (B) if a subset `X ⊆ L`
covers `p`, then there is an integer-valued `(f, g⁻ + χ_X)`-bounded `m`-flow. -/
theorem lemma_4_1 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (L : Finset A)
    (hS : Setting4 f g m L) :
    (∀ x ∈ intFlows D f g m, Covers D (satSet L g x) (pFun D m f g L)) ∧
    (∀ X : Finset A, X ⊆ L → Covers D X (pFun D m f g L) →
      ∃ x : A → ℤ, x ∈ intFlows D f (shiftOn (shiftOn g L (-1)) X 1) m) := by sorry

end FairFlows
