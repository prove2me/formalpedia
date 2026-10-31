-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_isMaxWeightIndep_iff
-- name    : CombOpt.MatroidPolytope.isMaxWeightIndep_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:43.838121+00:00
-- url     : https://prove2.me/theorems/520c7c39-bdc9-47fb-ae01-7c175e8553c9
-- title:
--   Corollary 8.6 — local optimality conditions for a maximum-weight independent set
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid, let $c\in\mathbb R^S$, and let $J\in\mathcal I$. Then $J$ is a maximum-weight independent set with respect to $c$ if and only if
--
--   1. $e\in J$ implies $c_e\ge 0$;
--   2. $e\notin J$ and $J\cup\{e\}\in\mathcal I$ imply $c_e\le 0$;
--   3. $e\notin J$, $f\in J$ and $(J\cup\{e\})\setminus\{f\}\in\mathcal I$ imply $c_e\le c_f$.
--
--   So optimality of an independent set can be certified by single-element deletions, additions and exchanges.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Corollary 8.6, p. 280 (PDF p. 287)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_IsMaxWeightIndep

namespace CombOpt.MatroidPolytope

/-- **Corollary 8.6: local optimality conditions for a maximum-weight independent set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Corollary 8.6, p. 280 (PDF p. 287): "Let M = (S, I) be a matroid, let c ∈ R^S, and let
J ∈ I. Then J is a maximum-weight independent set with respect to c if and only if
(a) e ∈ J implies c_e ≥ 0; (b) e ∉ J, J ∪ {e} ∈ I imply c_e ≤ 0; (c) e ∉ J, f ∈ J,
(J ∪ {e})\{f} ∈ I imply c_e ≤ c_f." -/
theorem isMaxWeightIndep_iff {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop)
    (hI : IsMatroid I) (c : α → ℝ) (J : Finset α) (hJ : I J) :
    IsMaxWeightIndep I c J ↔
      (∀ e ∈ J, 0 ≤ c e) ∧
        (∀ e, e ∉ J → I (insert e J) → c e ≤ 0) ∧
          (∀ e f, e ∉ J → f ∈ J → I ((insert e J).erase f) → c e ≤ c f) := by sorry

end CombOpt.MatroidPolytope
