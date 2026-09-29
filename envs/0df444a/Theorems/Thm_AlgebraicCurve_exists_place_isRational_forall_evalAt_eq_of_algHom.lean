-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_place_isRational_forall_evalAt_eq_of_algHom
-- name    : AlgebraicCurve.exists_place_isRational_forall_evalAt_eq_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/941c50b6-3469-593a-af9c-d5a445aaf22d
-- title:
--   A character of S is evaluation at a rational place
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field that is a $K$-algebra, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Assume $x \neq$ `algebraMap K F c` for every $c \in K$. Let $S$ be a $K$-subalgebra of $F$ with $x \in S$, assume that every $f \in S$ lies in the valuation subring of every rational place $w$ of $F/K$ whose valuation subring contains $x$, and let $\chi : S \to K$ be a $K$-algebra homomorphism. Then there is a place $r$ of $F/K$ — that is, a valuation subring $\mathcal{O}_r \subseteq F$ containing `algebraMap K F a` for all $a \in K$, different from $F$ itself, and a principal ideal ring — which is rational, meaning that $K \to \mathcal{O}_r/\mathfrak{m}_r$ is surjective, such that $x \in \mathcal{O}_r$ and such that for every $f \in S$ one has $f \in \mathcal{O}_r$ and $r.\mathrm{evalAt}(f) = \chi(f)$, where $r.\mathrm{evalAt}(f)$ is the element of $K$ obtained from the residue class of $f$ by a chosen inverse of the (surjective) map $K \to \mathcal{O}_r/\mathfrak{m}_r$.
--
--   This is the Chevalley-style statement that a $K$-valued character of an affine ring inside a one-variable function field over an algebraically closed field of constants is evaluation at a rational place. It is used in the treatment of modular curves, where characters of rings of functions on charts are converted into points, i.e. places at which $q$-expansions and other regular functions may be evaluated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_place_isRational_forall_evalAt_eq_of_algHom.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem AlgebraicCurve.exists_place_isRational_forall_evalAt_eq_of_algHom
    (K F : Type) [Field K] [IsAlgClosed K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F]
    (hx : ∀ c : K, x ≠ algebraMap K F c)
    (S : Subalgebra K F) (hxS : x ∈ S)
    (hS : ∀ f ∈ S, ∀ w : Place K F, w.IsRational → x ∈ w.toValuationSubring → f ∈ w.toValuationSubring)
    (χ : ↥S →ₐ[K] K) :
    ∃ r : Place K F, r.IsRational ∧ x ∈ r.toValuationSubring ∧
      ∀ f : ↥S, (f : F) ∈ r.toValuationSubring ∧ r.evalAt (f : F) = χ f := by sorry
