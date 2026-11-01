-- Prove2me | Theorems.Thm_FairFlows_beta_cap_reduction
-- name    : FairFlows.beta_cap_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:14.0359+00:00
-- url     : https://prove2.me/theorems/b9271c39-12bd-4e9b-bbba-82f1f4f8aa00
-- title:
--   §2.2, (2.4) — capping $g$ at $\beta_F$ preserves $F$-dec-min flows and makes $\max_F g=\beta_F$
-- statement:
--   Let $F\subseteq A$ be non-empty, $f$ and $g$ finite on $F$, $f\le g$, $\widetilde m(V)=0$, and Q⃛$(f,g;m)\neq\emptyset$. Let
--   $$\beta_F:=\min\{\max\{z(a):a\in F\}: z\in Q⃛(f,g;m)\}\qquad(2.4)$$
--   and let $g^\beta$ arise from $g$ by decreasing $g(e)$ to $\beta_F$ for each $e\in F$ with $g(e)>\beta_F$. Then:
--
--   1. the $F$-dec-min elements of Q⃛$(f,g;m)$ and of Q⃛$(f,g^\beta;m)$ coincide;
--   2. there is an integer-valued feasible $m$-flow after the decrease, Q⃛$(f,g^\beta;m)\neq\emptyset$;
--   3. $\max\{g^\beta(e): e\in F\}=\beta_F$;
--   4. $Q(f,g^-;m)=\emptyset$, where $g^-$ arises from $g^\beta$ by subtracting $1$ from $g^\beta(e)$ for each $e\in F$ with $g^\beta(e)=\beta_F$.
--
--   This is the reduction that lets the proof of Theorem 2.1 assume (5.1).
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: decreasingly minimal on F → no member of the set has a non-increasingly sorted value list on F that is lexicographically smaller (List.Lex (· < ·)); reason: Lean convention; this is the paper's definition
--   - reading: "we can assume that max{g(e) : e ∈ F} = β_F which is equivalent to requiring that Q(f, g; m) is non-empty but Q(f, g−; m) = ∅" → for g^β (g decreased to β_F on F): the F-dec-min flows are unchanged, Q⃛(f, g^β; m) ≠ ∅, max_F g^β = β_F and Q(f, g^β − χ; m) = ∅; reason: the paper's "we can assume" is a reduction; the four clauses are what it asserts about the capped bound, with (4) for real flows as printed; the converse reading of "equivalent" for an uncapped g (Q ≠ ∅ and Q(f, g−; m) = ∅ imply max_F g = β_F) is false (F = {e₁, e₂}, g(e₁) = 5, g(e₂) = 3, e₁ in series with a capacity-3 edge, z(e₁) + z(e₂) = 6) and is not stated
--   - encoding: the context of Theorem 2.1 (a real (f, g)-bounded m-flow exists) → Q⃛(f, g; m) ≠ ∅; reason: Q is an integral polyhedron for integral f, g, m (p.6), so the two hypotheses are equivalent
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §2.2, p.7, (2.4)

import Mathlib
import Definitions.Def_FairFlows_DecMin
import Definitions.Def_FairFlows_MaxMinimizer

set_option autoImplicit false

namespace FairFlows

/-- The capping step of §2.2 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.7, (2.4)). Let `F` be non-empty with `f`, `g` finite on
`F`, `f ≤ g`, `m̃(V) = 0`, and `Q⃛(f, g; m)` non-empty. Let
`β_F = min{max{z(a) : a ∈ F} : z ∈ Q⃛(f, g; m)}` (2.4) and let `g^β` arise from `g` by decreasing
`g(e)` to `β_F` for each `e ∈ F` with `g(e) > β_F`. Then
(i) the `F`-dec-min elements of `Q⃛(f, g; m)` and of `Q⃛(f, g^β; m)` are the same;
(ii) there is an integer-valued feasible `m`-flow after the decrease: `Q⃛(f, g^β; m) ≠ ∅`;
(iii) `max{g^β(e) : e ∈ F} = β_F`;
(iv) `Q(f, g⁻; m) = ∅`, where `g⁻` arises from `g^β` by subtracting `1` from `g^β(e)` for each
`e ∈ F` with `g^β(e) = β_F`.

**Formalization Note** (iv) is stated for real flows `Q`, as on p.7; it implies the integral
form `Q⃛(f, g⁻; m) = ∅` used in (5.1). -/
theorem beta_cap_reduction {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (hfg : BoundsLE f g) (hm : demandSum m Finset.univ = 0)
    (hF : ∀ e ∈ F, f e ≠ ⊥ ∧ g e ≠ ⊤) (hFne : F.Nonempty) (hQ : (intFlows D f g m).Nonempty) :
    (∀ z : A → ℤ, IsDecMinOn (intFlows D f g m) F z ↔
        IsDecMinOn (intFlows D f (capOn g F (betaF D f g m F)) m) F z) ∧
    (intFlows D f (capOn g F (betaF D f g m F)) m).Nonempty ∧
    ((∀ e ∈ F, capOn g F (betaF D f g m F) e ≤ ((betaF D f g m F : ℤ) : WithTop ℤ)) ∧
      ∃ e ∈ F, capOn g F (betaF D f g m F) e = ((betaF D f g m F : ℤ) : WithTop ℤ)) ∧
    feasFlows D f
      (shiftOn (capOn g F (betaF D f g m F))
        (F.filter (fun e => capOn g F (betaF D f g m F) e = ((betaF D f g m F : ℤ) : WithTop ℤ)))
        (-1)) m = ∅ := by sorry

end FairFlows
