-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
-- name    : CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/7cb51674-bbe3-5ef3-ad37-5a90cacea904
-- title:
--   Admissible edge regions cover the affinoid Ωₙ
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, and let $C$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$ (together with routine typeclass data, including decidable equality on $C$). Let $\varpi$ be a pseudo-uniformizer of $K_0$ relative to $C$, i.e. an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi.\varpi) < 1$ in $C$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume $\varpi_0 \in R$ is irreducible with $\varpi.\varpi$ its image in $K_0$, that $R/(\varpi_0)$ is finite, that $v(a) \le 1$ for every $a$ in the image of $R$, and conversely that every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$ (`IsLocalization.IsInteger`). Let $n \ge 1$. Write $\Omega_m$ for `affinoid ϖ m`, the set of $z \in C$ with $v(z) \le v(\varpi.\varpi)^{-m}$ and $v(z-a) \ge v(\varpi.\varpi)^{m}$ for all $a \in K_0$ with $v(a) \le v(\varpi.\varpi)^{-m}$. Call a triple $(c, m, g)$ with $c \in K_0$, $m \in \mathbb{Z}$ and $g \in \mathrm{GL}_2(K_0)$ admissible when the underlying matrix of $g$ is $!![\varpi.\varpi^{m-1}, c; 0, 1]$, $1 - n \le m \le n$ and $v(c) \le v(\varpi.\varpi^{-n})$, and set $E(g) =$ `vertexTube ϖ ḡ ∪ edgeTube ϖ ḡ ∪ vertexTube ϖ (ḡ·σ)`, where $\bar{\;}$ denotes the image in $\mathrm{PGL}_2(K_0)$, $\sigma$ is the class of $\mathrm{diag}(\varpi.\varpi, 1)$, `vertexTube ϖ h` is the set of $z \in C$ outside the image of $K_0$ with $h^{-1}z \in \Omega_0$ under the Möbius action, and `edgeTube ϖ h` is the set of such $z$ with $h^{-1}z$ outside the image of $K_0$ and $v(\varpi.\varpi) < v(h^{-1}z) < 1$. The theorem asserts the conjunction: (i) $E(g) \subseteq \Omega_n$ for every admissible $(c,m,g)$; and (ii) every $z \in \Omega_n$ lies in $E(g)$ for some admissible $(c,m,g)$.
--
--   This identifies the affinoid $\Omega_n$ of Drinfeld's $p$-adic upper half-plane with the union of the closed regions attached to the edges of the depth-$2n$ part of the Bruhat–Tits tree, each region being a vertex tube, an edge tube and the neighbouring vertex tube in the standard affine chart. It feeds the construction of covers of $\Omega_n$ by chains of such regions and, through that, the analytic input to the Čerednik–Drinfeld uniformisation of the relevant quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀), (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] →
      1 - (n : ℤ) ≤ m → m ≤ n → Valued.v (algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) →
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ)) ⊆ affinoid ϖ n) ∧
    (∀ z : C, z ∈ affinoid ϖ n → ∃ (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀),
      (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] ∧ 1 - (n : ℤ) ≤ m ∧ m ≤ n ∧
      Valued.v (algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) ∧
      z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) := by sorry
