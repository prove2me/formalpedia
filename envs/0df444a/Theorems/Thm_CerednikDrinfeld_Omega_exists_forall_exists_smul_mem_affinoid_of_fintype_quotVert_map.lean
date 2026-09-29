-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_exists_smul_mem_affinoid_of_fintype_quotVert_map
-- name    : CerednikDrinfeld.Omega.exists_forall_exists_smul_mem_affinoid_of_fintype_quotVert_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/cbc5125e-d94d-5775-ba33-f2c84182615c
-- title:
--   Finitely many vertex orbits force a single absorbing affinoid
-- statement:
--   Let $K_0$ be a field, $K$ a field equipped with a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$ and with a $K_0$-algebra structure. Let $R_0$ be a discrete valuation domain with finite residue field, with $K_0$ as its fraction field, and assume that an element $x\in K_0$ lies in the image of $R_0$ if and only if $v(x)\le 1$ in $K$. Let $\varpi$ be a pseudo-uniformiser: an element $\varpi\in K_0$ with $0<v(\varpi)<1$ such that for every $a\in K_0^\times$ there is $N$ with $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$; let $\varpi_0\in R_0$ be irreducible with image $\varpi$. Assume $\varpi$ is exhausted: every $z\in K$ outside the image of $K_0$ lies in some affinoid $\Omega_n=\{z: v(z)\le v(\varpi)^{-n}$ and $v(z-a)\ge v(\varpi)^n$ for all $a\in K_0$ with $v(a)\le v(\varpi)^{-n}\}$. Let $G$ be a group, $\rho\colon G\to \mathrm{PGL}_2(K_0)$ a homomorphism, $\Gamma\le G$ a subgroup, and assume the orbit quotient of the subgroup $\rho(\Gamma)$ acting on the vertices $\mathrm{Vertex}\,R_0\,K_0$ (homothety classes of full lattices) is finite. Then there is $N\in\mathbb N$ such that for every $z\in K$ outside the image of $K_0$ there is $\gamma\in\Gamma$ with $\rho(\gamma)\cdot z\in\Omega_N$. No completeness or algebraic closedness of $K$ is assumed.
--
--   This is the cocompactness statement on the Drinfeld upper half plane in its bare form: finiteness of the number of $\rho(\Gamma)$-orbits of vertices of the Bruhat–Tits tree of $\mathrm{PGL}_2(K_0)$ yields one affinoid in the exhaustion that meets every $\Gamma$-orbit. It is the hypothesis consumed by the rigidity statement that $\Gamma$-invariant holomorphic functions are constant, and it is used further in the Möbius-action reformulation and in the surjectivity of places on invariant function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_forall_exists_smul_mem_affinoid_of_fintype_quotVert_map.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.exists_forall_exists_smul_mem_affinoid_of_fintype_quotVert_map

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    (Γ : Subgroup G)
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))] :
    ∃ N : ℕ, ∀ z : ↥(Omega.upperHalfPlane K₀ K), ∃ γ ∈ Γ,
      ((ρ γ • z : ↥(Omega.upperHalfPlane K₀ K)) : K) ∈ Omega.affinoid ϖ N := by sorry
