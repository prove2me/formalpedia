-- Prove2me | Theorems.Thm_BregmanPPA_Existence_theorem4_image
-- name    : BregmanPPA.Existence.theorem4_image
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:57.866728+00:00
-- url     : https://prove2.me/theorems/8bc8665e-bd7b-452f-8ffe-c45b4fc29238
-- title:
--   Proof of Theorem 4 — in cases (i) and (ii), im ∇h ⊆ im(∇h + cT) for every c > 0
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $T:H\to2^H$ a maximal monotone operator, and $h$ a Bregman function with zone $S\supseteq\operatorname{dom}T$. Suppose that either
--
--   1. $\operatorname{im}\nabla h=\nabla h(S)$ is all of $H$, or
--   2. $\operatorname{im}\nabla h$ is open and $0\in\operatorname{im}T$.
--
--   Then for every $c>0$,
--   $$
--   \operatorname{im}\nabla h\ \subseteq\ \operatorname{im}(\nabla h+cT),
--   $$
--   that is, for every $y\in S$ there are $p\in S$ and $t\in T(p)$ with $\nabla h(y)=\nabla h(p)+c\,t$. Equivalently, $(\nabla h+cT)^{-1}\circ\nabla h$ is defined throughout $\operatorname{dom}\nabla h=S$, and its values lie in $\operatorname{dom}(\nabla h + cT)\subseteq S$.
--
--   This is the one-step existence statement that the induction in the proof of Theorem 4 iterates.
--
--   **Formalization Note** The page argues for $T$; the induction applies the argument to $c_kT$, which is maximal monotone with the same domain as $T$, and $0\in\operatorname{im}(c_kT)$ iff $0\in\operatorname{im}T$. The statement is therefore made for $cT$ with an arbitrary $c>0$. $\operatorname{im}\nabla h$ is the image $\nabla h(S)$ of the zone, not the range of Mathlib's total `gradient h`, which takes the junk value $0$ off the differentiability set. In case (i) the page concludes the stronger $\operatorname{im}(T+\nabla h)\supseteq\mathbb R^n$; the stated inclusion is what both cases give and what the induction uses.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 209, proof of Theorem 4, cases (i) and (ii)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_Existence_Operators

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace BregmanPPA.Existence

/-- Proof of Theorem 4 (p. 209), cases (i) and (ii): if `im ∇h = ℝⁿ`, or `im ∇h` is open and
`0 ∈ im T`, then for every `c > 0`, `im ∇h ⊆ im(∇h + cT)`; that is, `(∇h + cT)⁻¹ ∘ ∇h` is defined
throughout `dom ∇h = S`. -/
theorem theorem4_image {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hdom : dom T ⊆ S)
    (hcase : gradient h '' S = Set.univ ∨
      (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T))
    (c : ℝ) (hc : 0 < c) :
    gradient h '' S ⊆ imOp (opAdd (gradOp S h) (opSmul c T)) := by sorry

end BregmanPPA.Existence
