-- Prove2me | Theorems.Thm_FairFlows_theorem_5_1
-- name    : FairFlows.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:19.977492+00:00
-- url     : https://prove2.me/theorems/bc2b8515-a7d8-4a0b-aa86-7a6d3bb064d0
-- title:
--   Theorem 5.1 — a dual optimal chain characterizes pre-dec-min flows
-- statement:
--   Assume (5.1): $f\le g$, $\widetilde m(V)=0$, $f$ and $g$ finite on $F$, $F$ non-empty with no tight edges, $\beta:=\max\{g(e):e\in F\}$, $L:=\{e\in F:g(e)=\beta\}$, $g^-:=g-\chi_L$, Q⃛$=$Q⃛$(f,g;m)\neq\emptyset$ and Q⃛$(f,g^-;m)=\emptyset$. Then there is a chain $\mathcal C'$ of non-empty proper subsets $V_1\supset V_2\supset\cdots\supset V_q$ of $V$ with $\varrho_g(V_i)-\delta_f(V_i)<+\infty$ such that a member $z$ of Q⃛ is pre-dec-min on $F$ if and only if:
--
--   1. (O1) $z(e)=f(e)$ for every edge $e\in A$ leaving a member of $\mathcal C'$;
--   2. (O2) $z(e)=g(e)$ for every edge $e\in A-L$ entering a member of $\mathcal C'$;
--   3. (O3) $\beta-1\le z(e)\le\beta$ for every edge $e\in L$ entering exactly one member of $\mathcal C'$;
--   4. (O4) $z(e)=\beta$ for every edge $e\in L$ entering at least two members of $\mathcal C'$;
--   5. (O5) $f(e)\le z(e)\le\beta-1$ for every edge $e\in L$ neither entering nor leaving any member of $\mathcal C'$.
--
--   Such a chain is called a dual optimal chain.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: a chain V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q → a Finset of distinct subsets totally ordered by ⊆ (IsChain); "enters exactly one / at least two" counts members; reason: Lean convention; same instances
--   - generalization: §5 assumes the underlying undirected graph of D is connected (p.13) → no connectivity assumption; reason: nothing in §§4–5 uses it and Theorem 2.1 does not assume it; connected digraphs are the special case
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 5.1, pp.13–14 ((5.1) p.13)

import Mathlib
import Definitions.Def_FairFlows_Section5

set_option autoImplicit false

namespace FairFlows

/-- Theorem 5.1 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, pp.13–14). Given (5.1), there is a chain `C′` of non-empty proper
subsets `V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q` of `V` with `ϱ_g(Vᵢ) − δ_f(Vᵢ) < +∞` such that a member `z` of `Q⃛` is
pre-dec-min on `F` if and only if the optimality criteria (O1)–(O5) hold, i.e. there is a dual
optimal chain.

**Formalization Note** `Setting51` is (5.1) with the standing assumptions of §5 except the
connectivity of the underlying undirected graph, which is dropped. -/
theorem theorem_5_1 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (hS : Setting51 D f g m F) :
    ∃ C : Finset (Finset V), IsDualOptimalChain D f g m F C := by sorry

end FairFlows
