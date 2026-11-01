-- Prove2me | Theorems.Thm_FairFlows_theorem_4_6
-- name    : FairFlows.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:04.379563+00:00
-- url     : https://prove2.me/theorems/586df9a2-e5da-4eda-a806-feaf5882480e
-- title:
--   Theorem 4.6 — chain optimality criteria (O1)–(O5) for $L$-upper-minimizers
-- statement:
--   In the §4 setting ($\widetilde m(V)=0$, $f\le g$, $-\infty<f(e)<g(e)<+\infty$ on $L$), there is a chain $\mathcal C^*$ of subsets $V_1\supset V_2\supset\cdots\supset V_q$ of $V$ with $\varrho_g(V_i)-\delta_f(V_i)<+\infty$ such that an integer-valued $(f,g)$-bounded $m$-flow $z$ is an $L$-upper-minimizer if and only if:
--
--   1. (O1) $z(e)=f(e)$ for every edge $e\in A$ leaving a set $V_i$;
--   2. (O2) $z(e)=g(e)$ for every edge $e\in A-L$ entering a set $V_i$;
--   3. (O3) $g(e)-1\le z(e)\le g(e)$ for every edge $e\in L$ entering exactly one $V_i$;
--   4. (O4) $z(e)=g(e)$ for every edge $e\in L$ entering at least two $V_i$'s;
--   5. (O5) $f(e)\le z(e)\le g(e)-1$ for every edge $e\in L$ neither entering nor leaving any $V_i$.
--
--   Specialized to $L=\{e\in F: g(e)=\beta_F\}$ it gives Theorem 5.1.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: a chain V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q → a Finset of distinct subsets totally ordered by ⊆ (IsChain); "enters exactly one / at least two" counts members; reason: Lean convention; same instances
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 4.6, p.11

import Mathlib
import Definitions.Def_FairFlows_UpperMin

set_option autoImplicit false

namespace FairFlows

/-- Theorem 4.6 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.11). In the setting of §4 (`m̃(V) = 0`, `f ≤ g`,
`−∞ < f(e) < g(e) < +∞` on `L`), there is a chain `C* = {V₁ ⊃ ⋯ ⊃ V_q}` of subsets of `V` with
`ϱ_g(Vᵢ) − δ_f(Vᵢ) < +∞` such that an integer-valued `(f, g)`-bounded `m`-flow `z` is an
`L`-upper-minimizer if and only if it satisfies the optimality criteria (O1)–(O5). -/
theorem theorem_4_6 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (L : Finset A)
    (hS : Setting4 f g m L) :
    ∃ C : Finset (Finset V), IsChain (· ⊆ ·) (C : Set (Finset V)) ∧
      (∀ Z ∈ C, FiniteCut D f g Z) ∧
      ∀ z ∈ intFlows D f g m, (IsLUpperMin D f g m L z ↔ UpperMinCriteria D f g L C z) := by sorry

end FairFlows
