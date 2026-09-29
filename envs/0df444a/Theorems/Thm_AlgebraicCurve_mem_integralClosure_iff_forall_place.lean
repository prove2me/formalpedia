-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_integralClosure_iff_forall_place
-- name    : AlgebraicCurve.mem_integralClosure_iff_forall_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/f4b89ade-3632-5926-bd75-197f5e89d0b6
-- title:
--   Integral closure as intersection of the valuation rings of places
-- statement:
--   Let $k$ be a perfect field and let $K$ be a field equipped with a $k$-algebra structure which makes it a curve over $k$ in the sense of the predicate `IsCurveOver`, that is: every nonzero $f \in K$ has a divisor of degree $0$ whose value at each place is $\mathrm{ord}_v(f)$, every place has residue field finite-dimensional over $k$, and $\Omega_{K/k}$ is free of rank $1$ over $K$; assume moreover that $K$ is essentially of finite type over $k$. Here a place of $K$ over $k$ is a valuation subring $\mathcal{O}_v \subseteq K$ containing the image of $k$, different from $K$ itself, and whose ring structure is a principal ideal ring. The assertion is that, for every $k$-subalgebra $R \subseteq K$ and every $f \in K$, the element $f$ lies in the integral closure of $R$ in $K$ if and only if for every place $v$ of $K$ over $k$ such that the underlying set of $R$ is contained in $\mathcal{O}_v$ one has $f \in \mathcal{O}_v$. Equivalently, the integral closure of $R$ in $K$ is the intersection of the rings of those places of $K/k$ that contain $R$.
--
--   This is Krull's description of an integral closure as an intersection of valuation rings, specialised to a one-variable function field, where the relevant valuation rings are exactly the rings of places (holomorphy rings in the terminology of function-field theory). It is used in the identification of Riemann–Roch spaces attached to sets of places with modules spanned by integral closures, and in the integrality arguments for residues of $j$ and $q$-expansions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_integralClosure_iff_forall_place.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.mem_integralClosure_iff_forall_place
    {k : Type u} [Field k] [PerfectField k] {K : Type v} [Field K] [Algebra k K]
    [IsCurveOver k K] [Algebra.EssFiniteType k K]
    (R : Subalgebra k K) (f : K) :
    f ∈ integralClosure R K ↔
      ∀ v : Place k K, (R : Set K) ⊆ v.toValuationSubring → f ∈ v.toValuationSubring := by sorry
