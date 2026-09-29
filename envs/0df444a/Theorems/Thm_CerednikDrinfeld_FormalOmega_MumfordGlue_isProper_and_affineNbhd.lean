-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_and_affineNbhd
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_and_affineNbhd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/32738a30-e3d2-5cd8-a9bf-f33a20896bfa
-- title:
--   Properness and affine neighbourhoods in the Mumford glue tower
-- statement:
--   Fix a prime $r$ and a commutative domain $\mathcal O$ assumed to be a discrete valuation ring, an irreducible element $\pi \in \mathcal O$ such that the residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and a field $K_0$ that is a fraction field of $\mathcal O$. Let $g_1 \in \mathrm{GL}_2(K_0)$ be the element whose matrix is $\operatorname{diag}(\pi,1)$, let $N$ be a subgroup of $\mathrm{PGL}_2(K_0)$, and let `Gl` be a term of the structure `MumfordGlue` for these data: a family of schemes $Z_n$ together with morphisms $\mathtt{zb}_n : Z_n \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ that are flat and separated, transition morphisms $\mathtt{zt}_n : Z_n \to Z_{n+1}$ exhibiting $Z_n$ as the pullback of $Z_{n+1}$ along the base reduction $\mathcal O/(\pi^{n+2}) \to \mathcal O/(\pi^{n+1})$, and, for each $h \in \mathrm{GL}_2(K_0)$ and each $n$, a chart $\zeta_{h,n}$ from the spectrum of `chartERing` $\mathcal O\,\pi\,r$ modulo $\pi^{n+1}$ into $Z_n$, these charts being open immersions over the base, compatible with the transition morphisms, invariant under left translation by elements of $\mathrm{GL}_2(K_0)$ whose class lies in $N$, covering $Z_n$ by finitely many of them, and subject to the relations of the field `ζ_rel` describing chart points in terms of Deligne data. The conclusion is the conjunction of two assertions: each $\mathtt{zb}_n$ is proper, and for every $n$ and every finite subset $S \subseteq Z_n$ there is an affine open $U$ of $Z_n$ with $S \subseteq U$.
--
--   These are the two geometric properties of the levels of Mumford's formal glueing construction that allow the tower $(Z_n)$ to be algebraised into a formal scheme and then into a $\pi$-adic family of curves over $\mathcal O$; the second assertion is the standard device for producing a global affine cover compatible with a finite set of prescribed points. The result is used in the construction of a nonempty Mumford tower attached to a Schottky-type subgroup, [`CerednikDrinfeld.FormalOmega.nonempty_mumfordTower_of_isSchottky`](thm.html#CerednikDrinfeld.FormalOmega.nonempty_mumfordTower_of_isSchottky).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_and_affineNbhd.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_and_affineNbhd
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N) :
    (∀ n : ℕ, IsProper (Gl.zb n)) ∧
    (∀ (n : ℕ) (S : Set (Gl.Z n)), S.Finite → ∃ U : (Gl.Z n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z n))) := by sorry
