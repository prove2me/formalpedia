-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq
-- name    : AlgebraicCurve.Divisor.existsUnique_pullbackConstants_eq_of_forall_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/cd3e1f47-c9d8-5a1d-b8da-e44c7303b086
-- title:
--   Schmidt descent for G-invariant divisors of a constant field extension
-- statement:
--   Let $k$ be a perfect field, $K$ an algebraically closed field, and $F_0$, $F$ fields, equipped with algebra structures $k \to F_0$, $k \to K$, $K \to F$, $F_0 \to F$, $k \to F$ making $k \subseteq K \subseteq F$ and $k \subseteq F_0 \subseteq F$ towers, with $K/k$ algebraic and $F/F_0$ integral. Assume `IsCurveOver k F₀` and `IsCurveOver K F`: in each case every nonzero element has a degree-zero divisor recording its order at every place, every place has residue field finite-dimensional over the base field, and the module of Kähler differentials is free of rank one over the function field; here a place is a valuation subring of the function field containing the base field, distinct from the whole field and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Assume further: $F_0$ is generated over $k$ by a finite set; $F$ is generated over $K$, as an intermediate field, by the image of $F_0$; and $K$ and $F_0$ are linearly disjoint over $k$ in $F$, in the form that for $f \colon \mathrm{Fin}\,n \to F_0$ linearly independent over $k$ and $c \colon \mathrm{Fin}\,n \to K$ with $\sum_i c_i f_i = 0$ in $F$ one has $c_i = 0$ for all $i$. Let $G$ be a subgroup of [`AlgebraicCurve.SemilinearAut K F`](def/AlgebraicCurve_BaseChangeGalois.html#L15), the group of pairs consisting of a ring automorphism of $F$ and one of $K$ that are compatible with $K \to F$, and suppose every $g \in G$ fixes the image of $F_0$ in $F$ pointwise, while every $a \in K$ fixed by the $K$-component `baseAut g` of all $g \in G$ lies in the image of $k$. Then for every divisor $D$ of $F/K$ with $g \bullet D = D$ for all $g \in G$ there is a unique divisor $D_0$ of $F_0/k$ whose constant-field pullback [`AlgebraicCurve.Divisor.pullbackConstants K F D₀`](def/AlgebraicCurve_ConstantFieldPullback.html#L176) — the additive map sending a place $v$ of $F_0/k$ with multiplicity $n$ to $\sum_W n\,e(W)\,W$, the sum over the places $W$ of $F/K$ in the constant-field fibre above $v$, weighted by the ramification index of $W$ over $F_0$ — equals $D$.
--
--   This is the divisor-level statement of F. K. Schmidt's descent for constant field extensions: for a function field $F_0/k$ with $k$ perfect and full constant field $k$, and $F = F_0K$ with $K$ an algebraic closure of $k$, the divisors of $F/K$ invariant under a group of semilinear automorphisms fixing $F_0$ and with fixed field $k$ on $K$ are exactly the conorms of divisors of $F_0/k$, uniquely so. It is used in the count of Frobenius fixed points on the degree-zero divisor class group, [`AlgebraicCurve.Pic0.natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius`](thm.html#AlgebraicCurve.Pic0.natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.existsUnique_pullbackConstants_eq_of_forall_smul_eq
    {k K F₀ F : Type*} [Field k] [PerfectField k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
    [Algebra.IsAlgebraic k K] [Algebra.IsIntegral F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (G : Subgroup (AlgebraicCurve.SemilinearAut K F))
    (hG₀ : ∀ g ∈ G, ∀ x : F₀, g • algebraMap F₀ F x = algebraMap F₀ F x)
    (hGK : ∀ a : K, (∀ g ∈ G, AlgebraicCurve.SemilinearAut.baseAut g a = a) →
      a ∈ Set.range (algebraMap k K))
    (D : AlgebraicCurve.Divisor K F) (hD : ∀ g ∈ G, g • D = D) :
    ∃! D₀ : AlgebraicCurve.Divisor k F₀,
      AlgebraicCurve.Divisor.pullbackConstants K F D₀ = D := by sorry
