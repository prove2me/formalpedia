-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_resolvent_single_valued_full_domain
-- name    : DouglasRachfordPPA.GenDR.resolvent_single_valued_full_domain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:23:00.79325+00:00
-- url     : https://prove2.me/theorems/8e45ff9a-f95a-48d7-8172-f094e42859df
-- title:
--   Corollary 2.2 — the resolvent of a monotone operator is single-valued, with full domain if maximal
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $c>0$, and $T$ an operator on $\mathcal H$ with resolvent $J_{cT}=(I+cT)^{-1}$.
--
--   1. If $T$ is monotone, then $J_{cT}$ is single-valued.
--   2. If $T$ is maximal monotone, then $J_{cT}$ has full domain.
--   3. Consequently, if $T$ is maximal monotone there is exactly one map $J:\mathcal H\to\mathcal H$ with $\tfrac1c\,(x-J(x))\in T(J(x))$ for every $x$, that is, $x\in J(x)+cT(J(x))$.
--
--   Item 3 restates items 1–2 as existence and uniqueness of the resolvent as a function; it is what makes the resolvent maps $J_{\lambda A}$, $J_{\lambda B}$, $J_{c_kT}$ in Theorems 3, 6 and 7 well defined.
--
--   **Formalization Note** Items 1–2 are the paper's sentences for the graph resolvent `opResolvent c T`. Item 3 uses the published predicate `IsResolvent c T J`; it is the function-level reading of "single-valued with full domain" and adds no content beyond items 1–2.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 8, Corollary 2.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Corollary 2.2: for `c > 0` the resolvent `J_{cT}` of a monotone operator is single-valued;
if `T` is maximal monotone it has full domain. The third conjunct restates the maximal case as
existence and uniqueness of a resolvent function `J : H → H`. -/
theorem resolvent_single_valued_full_domain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T → IsSingleValuedOp (opResolvent c T)) ∧
    (IsMaximalMonotone T → dom (opResolvent c T) = Set.univ) ∧
    (IsMaximalMonotone T → ∃! J : H → H, IsResolvent c T J) := by sorry

end DouglasRachfordPPA.GenDR
