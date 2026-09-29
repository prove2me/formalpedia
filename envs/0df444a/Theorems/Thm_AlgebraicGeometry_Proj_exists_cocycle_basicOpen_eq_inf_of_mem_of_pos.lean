-- Prove2me | Theorems.Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
-- name    : AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/67cf154f-ac0a-5b31-8de8-9e8328ebda3a
-- title:
--   Transition cocycle for D₊(Fᵢ) on ProjA
-- statement:
--   Let $A$ be a commutative ring graded by $\mathcal{A} : \mathbb{N} \to \sigma$, where $\sigma$ is a `SetLike` family of additive subgroups of $A$ making $A$ a graded ring, let $d$ be a natural number with $0 < d$, and let $F : \mathrm{Fin}\,r \to A$ be a finite family with $F i \in \mathcal{A}_d$ for every $i$. Write $P = \operatorname{Proj}\mathcal{A}$ and $V_i = D_+(F i)$ for the homogeneous basic open of $F i$. The assertion is that there is a family of sections $w_{ij} \in \Gamma(P, V_i)$, indexed by pairs $i, j$, with the four properties: each $V_i$ is an affine open of $P$; $w_{ii} = 1$ in $\Gamma(P, V_i)$; for all $i, j, k$ the restriction of $w_{ik}$ to $V_i \sqcap V_j$ equals the product of the restriction of $w_{ij}$ from $V_i$ and the restriction of $w_{jk}$ from $V_j$, all three restrictions being the presheaf maps along the inclusions $V_i \sqcap V_j \le V_i$ and $V_i \sqcap V_j \le V_j$; and the scheme-theoretic basic open of the section $w_{ij}$ inside $V_i$ is exactly $V_i \sqcap V_j$. Note that $w_{ij}$ lives on $V_i$ (not on the intersection), and that the index set may be empty.
--
--   This packages the standard chart datum of $\mathcal{O}(d)$ on $\operatorname{Proj}\mathcal{A}$ relative to homogeneous elements $F_i$ of a common positive degree: the degree-zero ratios $F_j/F_i$ form a multiplicative cocycle whose non-vanishing locus is precisely $D_+(F_i) \cap D_+(F_j)$, and the charts $D_+(F_i)$ are affine. It feeds the construction of immersions into projective space used in the quasi-projectivity input of the wider development, being cited by [`AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`](thm.html#AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj) and [`AlgebraicGeometry.exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing`](thm.html#AlgebraicGeometry.exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization

theorem AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
    {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {d : ℕ} (hd : 0 < d) {r : ℕ} (F : Fin r → A) (hF : ∀ i : Fin r, F i ∈ 𝒜 d) :
    ∃ w : ∀ i j : Fin r, Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F i)),
      (∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i))) ∧
      (∀ i : Fin r, w i i = 1) ∧
      (∀ i j k : Fin r,
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i k) =
          (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i j) *
            (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F j))).op (w j k)) ∧
      (∀ i j : Fin r, (Proj 𝒜).basicOpen (w i j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j)) := by sorry
