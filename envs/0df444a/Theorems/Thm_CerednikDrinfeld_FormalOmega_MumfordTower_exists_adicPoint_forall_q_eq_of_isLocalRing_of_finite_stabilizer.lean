-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer
-- name    : CerednikDrinfeld.FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/1cf9c758-bfdd-5e67-8844-4bd0c5a0dd40
-- title:
--   Adic points lift Mumford-tower families over a local base
-- statement:
--   Fix a prime $r$, a characteristic-zero domain $\mathcal O$ assumed to be a discrete valuation ring, an irreducible $\pi \in \mathcal O$ with $\mathcal O$ complete for the $\pi$-adic topology, residue ring of cardinality $r$ and $(r) = (\pi)$, and a characteristic-zero field $K_0$ that is the fraction field of $\mathcal O$; let $g_1 \in \mathrm{GL}_2(K_0)$ be the diagonal matrix $\mathrm{diag}(\pi,1)$ and $N \le \mathrm{PGL}(2,K_0)$ a subgroup such that for every vertex $v$ of the lattice tree of $\mathcal O$ in $K_0$ (full lattices modulo homothety) the set of $g \in N$ with $g \cdot v = v$ is finite. Let $\mathrm{DM}$ be a Mumford tower for these data: schemes $Z_n$ with structure morphisms $zb_n : Z_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$, transition morphisms $zt_n : Z_n \to Z_{n+1}$ exhibiting the indicated pullback squares, $zb_n$ proper and flat, finite subsets of $Z_n$ contained in affine opens, together with maps $q_n$ sending a Deligne datum over an $\mathcal O$-algebra $B$ with $\pi^{n+1} = 0$ to a $B$-point of $Z_n$, compatible with base change, with the tower and invariant under pullback along elements of $N$. Let $R$ be a local $\mathcal O$-algebra, and write $R_n = R/(\pi^{n+1})$, assuming $\pi^{n+1} = 0$ in $R_n$ for all $n$. Two assertions are made. First, every family of morphisms $\eta_n : \operatorname{Spec} R_n \to Z_n$ which lies over $\operatorname{Spec}\mathcal O/\pi^{n+1}$ in the sense that $\eta_n$ followed by $zb_n$ followed by $\operatorname{Spec}$ of $\mathcal O \to \mathcal O/\pi^{n+1}$ is $\operatorname{Spec}$ of $\mathcal O \to R_n$, and which is compatible with the tower in the sense that $\operatorname{Spec}$ of the transition $R_{n+1} \to R_n$ followed by $\eta_{n+1}$ equals $\eta_n$ followed by $zt_n$, is of the form $\eta_n = q_n(x_n)$ for some adic point $x$ of the formal upper half plane over $R$, i.e. a family $x_n$ of Deligne data over the $R_n$ compatible under the transition maps. Second, two adic points $x, x'$ satisfy $q_n(x_n) = q_n(x'_n)$ for all $n$ if and only if there is a single $g \in \mathrm{GL}_2(K_0)$ whose class lies in $N$ such that, for every $n$ and every full lattice $M$, the line of $x'_n$ at $M$ is the preimage of the line of $x_n$ at $g^{-1}M$ under the base-changed action of $g^{-1}$.
--
--   This is the representability and uniqueness step in the Čerednik–Drinfeld description of the Mumford tower: the $\pi$-adic points of the tower over a local base are exactly the images of Deligne data on the formal upper half plane, and the fibres of the period map are single $N$-orbits. It is used in the construction of the descended quotient map on adic fibres, [`CerednikDrinfeld.FormalOmega.descendedQuotientMap_adicFib`](thm.html#CerednikDrinfeld.FormalOmega.descendedQuotientMap_adicFib).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer.lean

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))

    (hNfin : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ N ∧ g • v = v})
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra 𝒪 R]
    (hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0) :
    (∀ η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ DM.Z n,
      (∀ n : ℕ, η n ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n)))) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ DM.zt n) →
      ∃ x : AdicPoint K₀ π R, ∀ n : ℕ, η n = DM.q n (modPow π R n) (hmod n) (x.pt n)) ∧
    (∀ x x' : AdicPoint K₀ π R,
      (∀ n : ℕ, DM.q n (modPow π R n) (hmod n) (x.pt n) = DM.q n (modPow π R n) (hmod n) (x'.pt n)) ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
        ∀ n : ℕ, DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) g⁻¹ (x.pt n) (x'.pt n)) := by sorry
