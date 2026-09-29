-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
-- name    : AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/cc9e27a5-5686-531e-890d-8f31585985f4
-- title:
--   Vanishing of alternating Čech data above the number of charts
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} R$ a morphism, let $F$ be an `OModulePresheaf` for $\pi$ (an assignment of an $R$-module and $\Gamma(V,U)$-module $F(U)$ to each open $U\subseteq V$, the two actions being compatible via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps that are semilinear for restriction of sections and satisfy the identity and composition laws), and let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$, opens $U_j$ that are affine, with $\bigsqcup_j U_j=\top$. Put $n=\#\iota$. Then four statements hold simultaneously. First, for every $i\ge n$ the index type $K.Idx\,i$ of strictly monotone maps $\mathrm{Fin}(i+1)\to\iota$ is empty. Second, for every $i\ge n$ the degree-$i$ alternating cochain module $F.cochain\,K\,i=\prod_{s\in K.Idx\,i}F\bigl(\bigcap_j U_{s(j)}\bigr)$ is a subsingleton. Third, for every $i$ with $i+1\ge n$ the module $F.HSucc\,K\,i=\ker d^{i+1}/\operatorname{im}d^{i}$ is a subsingleton. Fourth, if $R$ is nontrivial then $F.cechFinrank\,K\,i$ — the $R$-rank of $F.H0\,K$ for $i=0$ and of $F.HSucc\,K\,(i-1)$ for $i>0$ — vanishes for all $i\ge n$, and for every $N\ge n$ one has $F.eulerChar\,K=\sum_{i<N}(-1)^i\,F.cechFinrank\,K\,i$, the Euler characteristic being defined as this sum with cut-off $N=n$.
--
--   This is the standard vanishing of alternating Čech cochains and cohomology in degrees at least the number of charts of a finite cover, together with the resulting independence of the Euler characteristic from the cut-off chosen in its defining alternating sum. It is used by the additivity of Čech Euler characteristics along short exact sequences and by the comparison results for Euler characteristics under pullback and tensoring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) := by sorry
