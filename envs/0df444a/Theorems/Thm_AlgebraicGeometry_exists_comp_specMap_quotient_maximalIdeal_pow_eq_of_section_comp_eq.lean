-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
-- name    : AlgebraicGeometry.exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/74819fad-42ec-59a2-86bf-4fc0714a5e92
-- title:
--   Factoring through an infinitesimal neighbourhood of a rational point
-- statement:
--   Let $k$ be a field, let $P$ be a scheme with a morphism $p \colon P \to \operatorname{Spec} k$, and let $P_0 \colon \operatorname{Spec} k \to P$ be a section of $p$ (i.e. $P_0$ followed by $p$ is the identity). Fix $n \in \mathbb{N}$, write $\mathcal{O}$ for the stalk of $P$ at the image under the underlying map of $P_0$ of the closed point of $\operatorname{Spec} k$, $\mathfrak{m}$ for its maximal ideal, and $A = \mathcal{O}/\mathfrak{m}^n$. Let $j_n \colon \operatorname{Spec} A \to P$ be a morphism assumed equal to $\operatorname{Spec}$ of the quotient map $\mathcal{O} \to A$ followed by the canonical morphism $\operatorname{Spec} \mathcal{O} \to P$; let $g \colon \operatorname{Spec} A \to \operatorname{Spec} k$ with $j_n$ followed by $p$ equal to $g$, and let $\sigma \colon \operatorname{Spec} k \to \operatorname{Spec} A$ satisfy $\sigma$ followed by $j_n$ equals $P_0$. Let $y \colon Y \to \operatorname{Spec} k$ with $Y$ quasi-compact and quasi-separated as a topological space, and let $\iota \colon Y \to Y \times_{\operatorname{Spec} k} \operatorname{Spec} A$ (the pullback of $y$ and $g$) have first component the identity of $Y$ and second component $y$ followed by $\sigma$. Then for every $\alpha \colon Y \times_{\operatorname{Spec} k} \operatorname{Spec} A \to P$ with $\iota$ followed by $\alpha$ equal to $y$ followed by $P_0$, there exists $\beta \colon Y \times_{\operatorname{Spec} k} \operatorname{Spec} A \to \operatorname{Spec} A$ with $\beta$ followed by $j_n$ equal to $\alpha$. Only existence of the factorisation is asserted, not its uniqueness.
--
--   This is the infinitesimal rigidity statement that a morphism from $Y \times_k \operatorname{Spec}(\mathcal{O}_{P,P_0}/\mathfrak{m}^n)$ to $P$ which is constant equal to the rational point $P_0$ along $Y$ factors through the $(n-1)$-st infinitesimal neighbourhood of $P_0$, in the style of the theory of formal neighbourhoods of a point of a group scheme or of a general $k$-scheme. It is used in the study of jets of partial actions, in the construction of an element of a general linear group matching a prescribed action, via a flat base change computation on global sections of the pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
    {k : Type u} [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    (P₀ : Spec (CommRingCat.of k) ⟶ P) (hP₀ : P₀ ≫ p = 𝟙 _) (n : ℕ)
    (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
        IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)) ⟶ P)
    (hjn : jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _)
    (g : Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
        IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)) ⟶
        Spec (CommRingCat.of k))
    (hg : jn ≫ p = g)
    (σ : Spec (CommRingCat.of k) ⟶
      Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
        IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)))
    (hσ : σ ≫ jn = P₀)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y]
    (ι : Y ⟶ pullback y g) (hι₁ : ι ≫ pullback.fst y g = 𝟙 Y)
    (hι₂ : ι ≫ pullback.snd y g = y ≫ σ)
    (α : pullback y g ⟶ P) (hα : ι ≫ α = y ≫ P₀) :
    ∃ β : pullback y g ⟶
        Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)),
      β ≫ jn = α := by sorry
