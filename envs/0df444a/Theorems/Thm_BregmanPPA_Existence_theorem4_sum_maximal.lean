-- Prove2me | Theorems.Thm_BregmanPPA_Existence_theorem4_sum_maximal
-- name    : BregmanPPA.Existence.theorem4_sum_maximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:54.508467+00:00
-- url     : https://prove2.me/theorems/29505a59-5f9c-41ad-8129-527fdee695db
-- title:
--   Proof of Theorem 4 — ∂h + T = ∇h + T is maximal monotone, and ∇h has the L-property
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $T:H\to2^H$ a maximal monotone operator, and $h$ a Bregman function with zone $S\supseteq\operatorname{dom}T$. Let $\hat h$ be the extension of $h$ by $+\infty$ off $\bar S$, so that $\partial h:=\partial\hat h$, and let $\nabla h$ denote the operator $x\mapsto\{\nabla h(x)\}$ on $S$ (empty off $S$). Then
--
--   1. $\partial h+T=\nabla h+T$;
--   2. $\nabla h+T$ is maximal monotone;
--   3. $\nabla h$ has the L-property.
--
--   Here $(A+B)(x)=\{a+b : a\in Ax,\ b\in Bx\}$. These are conditions (b) and (c) of the Brézis–Haraux theorem (Theorem 3) for $A=T$ and $B=\nabla h$; condition (a) is the hypothesis $\operatorname{dom}T\subseteq S$.
--
--   **Formalization Note** The paper writes $\partial h$ for the subdifferential of the closed proper convex function obtained by setting $h=+\infty$ off $\bar S$ (note after Definition 1, p. 205); this is `subdiffOp (extendedFn S h)`. The hypothesis is $S\supseteq\operatorname{dom}T$ without closures, as printed in Theorem 4. The paper cites the maximality of $\partial h$ [27] and the relative-interior sum theorem [28] as known results; they are not separate items.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 209, proof of Theorem 4 (conditions (a)–(c) of Theorem 3)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_Existence_Operators
import Definitions.Def_BregmanPPA_Existence_LProperty

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace BregmanPPA.Existence

/-- Proof of Theorem 4 (p. 209): for `T` maximal monotone and `h` a Bregman function with zone
`S ⊇ dom T`, the operator `∇h + T` (domain `S ∩ dom T`) is maximal monotone and coincides with
`∂h + T`, where `∂h` is the subdifferential of the extension `ĥ` of `h` by `+∞` off `S̄`; and the
operator `∇h` has the L-property. -/
theorem theorem4_sum_maximal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hdom : dom T ⊆ S) :
    opAdd (BregmanPPA.Convergence.subdiffOp (extendedFn S h)) T = opAdd (gradOp S h) T ∧
    IsMaximalMonotone (opAdd (gradOp S h) T) ∧
    HasLProperty (gradOp S h) := by sorry

end BregmanPPA.Existence
