-- Prove2me | Theorems.Thm_FairFlows_lemma_4_2
-- name    : FairFlows.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:26.757535+00:00
-- url     : https://prove2.me/theorems/9c9b3332-965d-4fac-8ed6-f13b5ddd125f
-- title:
--   Lemma 4.2 — $L$-upper-minimizers are exactly the flows whose saturated set is a smallest cover of $p$
-- statement:
--   In the §4 setting ($\widetilde m(V)=0$, $f\le g$, $-\infty<f(e)<g(e)<+\infty$ on $L$, and $p$ from (4.2)), an integer-valued $(f,g)$-bounded $m$-flow $x$ is an $L$-upper-minimizer (its number of $g$-saturated edges in $L$ is as small as possible) if and only if $X:=\{e\in L: x(e)=g(e)\}$ is a smallest subset of $L$ covering $p$.
--
--   This translates the flow problem into the supermodular covering problem of §3.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Lemma 4.2, p.10 (Claims 4.3, 4.4)

import Mathlib
import Definitions.Def_FairFlows_UpperMin

set_option autoImplicit false

namespace FairFlows

/-- Lemma 4.2 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.10). In the setting of §4, an integer-valued `(f, g)`-bounded
`m`-flow `x` is an `L`-upper-minimizer if and only if `X := {e ∈ L : x(e) = g(e)}` is a smallest
subset of `L` covering `p` (4.2). -/
theorem lemma_4_2 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (L : Finset A)
    (hS : Setting4 f g m L) :
    ∀ x ∈ intFlows D f g m,
      (IsLUpperMin D f g m L x ↔ IsMinCover D L (satSet L g x) (pFun D m f g L)) := by sorry

end FairFlows
