-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback_of_isLocalRing
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/dc5e347d-6d1a-54d1-969c-52cc851a10e1
-- title:
--   N-related Deligne data give equal chart points over local rings
-- statement:
--   Fix a prime $r$ and a domain $\mathcal O$ that is a discrete valuation ring, with $\pi \in \mathcal O$ irreducible and residue ring $\mathcal O/(\pi)$ of cardinality $r$, and let $K_0$ be a fraction field of $\mathcal O$. Let $g_1 \in \mathrm{GL}_2(K_0)$ have matrix $\mathrm{diag}(\pi, 1)$, and let $N \le \mathrm{PGL}_2(K_0)$ be a subgroup that is Schottky for the Bruhat–Tits tree of homothety classes of full $\mathcal O$-lattices in $K_0^2$ (trivial vertex stabilisers, no dart sent to its reverse, finitely many vertex and dart orbits) and which preserves the type, i.e. the parity of the distance from the standard vertex. Let $M$ be a `MumfordGlueCore` for the data $(\mathcal O, \pi, K_0, r, g_1, N)$, with schemes $Z n$ and charts $M.\zeta$. The assertion is: for every $n$, every local $\mathcal O$-algebra $B$, all $h, h' \in \mathrm{GL}_2(K_0)$, all $\mathcal O$-algebra maps $x_q, x_q'$ from $A_n := \mathrm{chartERing}\,\mathcal O\,\pi\,r$ modulo $(\pi^{n+1})$ to $B$, and all Deligne data $d, d', P, P'$ over $B$ for $(\pi, K_0)$, suppose that $d$ lies in the standard edge position prescribed by $x_q$: its line at the standard full lattice is the $B$-span of $\bar x_q(\xi)\otimes e_0 + 1 \otimes e_1$, its line at $g_1 \cdot (\text{standard lattice})$ is the image under the base-changed action of $g_1$ of the span of $1 \otimes e_0 + \bar x_q(\eta) \otimes e_1$ (where $\bar x_q$ denotes $x_q$ precomposed with the quotient map), and $d$ satisfies the edge-chart nondegeneracy condition at the pair $(g_1 \cdot \text{std}, \text{std})$ for every prime ideal of $B$; suppose the same three conditions for $d'$ with $x_q'$; suppose $P$ is the pullback of $d$ along $h^{-1}$ and $P'$ the pullback of $d'$ along $h'^{-1}$ (in each case: at every full lattice $L$ the line is the preimage of the line at $g^{-1}L$ under the base-changed action); and suppose some $g \in \mathrm{GL}_2(K_0)$ with class in $N$ exhibits $P'$ as the pullback of $P$ along $g^{-1}$. Then the morphism $\mathrm{Spec}\,B \to \mathrm{Spec}\,A_n$ induced by $x_q$ followed by $M.\zeta\,h\,n$ agrees with the morphism induced by $x_q'$ followed by $M.\zeta\,h'\,n$.
--
--   This is the local form of the chart-gluing dictionary for Mumford's construction: Deligne data that differ by an element of the Schottky group $N$ are carried to the same $B$-point of the $n$-th layer $Z n$ of the gluing core. It supplies one implication of the equivalence [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_iff_exists_isPullback_of_isLocalRing`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_iff_exists_isPullback_of_isLocalRing), the local base case of the relation law governing overlaps of the charts $\zeta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback_of_isLocalRing.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback_of_isLocalRing
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))
    (M : MumfordGlueCore 𝒪 π K₀ r g₁ N) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
      Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n := by sorry
