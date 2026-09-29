-- Prove2me | Theorems.Thm_AlgHom_bijective_and_free_of_length_le_of_levelChange
-- name    : AlgHom.bijective_and_free_of_length_le_of_levelChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/46c51d2c-e959-5ae2-baa7-abb4f605d99c
-- title:
--   Numerical criterion transported across a level change
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a domain, discretely valued, adically complete for its maximal ideal). At the "old" level: $T$ is a commutative $\mathcal O$-algebra with an $\mathcal O$-algebra map $\pi_T\colon T\to\mathcal O$ whose kernel $\wp$ satisfies $\pi_T(\operatorname{Ann}_T\wp)\neq 0$; $M$ is a $T$-module, finite and free over $\mathcal O$ with compatible scalars, carrying an $\mathcal O$-bilinear $B\colon M\times M\to\mathcal O$ with $B(tm,n)=B(m,tn)$ for all $t\in T$ and with $m\mapsto B(m,-)$ a bijection onto $\operatorname{Hom}_{\mathcal O}(M,\mathcal O)$; $\pi_{R_0}\colon R_0\to\mathcal O$ is an augmented commutative $\mathcal O$-algebra, and in $\mathbb N^\infty$ one assumes $\operatorname{rank}_{\mathcal O}M[\wp]\cdot\ell_{\mathcal O}(\ker\pi_{R_0}/(\ker\pi_{R_0})^2)\le\ell_{\mathcal O}\bigl(M/(M[\wp]+M[\operatorname{Ann}_T\wp])\bigr)$, where $M[S]$ denotes the $S$-torsion submodule. At the "new" level: $R'$ is a Noetherian local $\mathcal O$-algebra, adically complete for its maximal ideal, $T'$ a local $\mathcal O$-algebra finite and free over $\mathcal O$, $\varphi'\colon R'\to T'$ a surjective $\mathcal O$-algebra map, $\pi_{R'},\pi_{T'}$ augmentations with $\pi_{T'}\circ\varphi'=\pi_{R'}$ and $\pi_{T'}(\operatorname{Ann}_{T'}\wp')\neq 0$ for $\wp'=\ker\pi_{T'}$, and $M'$ a $T'$-module, finite free over $\mathcal O$, with a perfect $T'$-invariant pairing $B'$, such that $M'[\wp']\neq 0$ and $\operatorname{rank}_{\mathcal O}M'=\operatorname{rank}_{\mathcal O}M'[\wp']\cdot\operatorname{rank}_{\mathcal O}T'$. The levels are linked by $\mathcal O$-linear $i\colon M\to M'$ and $j\colon M'\to M$ adjoint for the pairings, $B(jm',m)=B'(m',im)$, with $j\circ i$ equal to multiplication by some $\Delta\in T$ with $\pi_T(\Delta)\neq 0$, and $i(M[\wp])=M'[\wp']$ as $\mathcal O$-submodules; finally $\ell_{\mathcal O}(\ker\pi_{R'}/(\ker\pi_{R'})^2)\le\ell_{\mathcal O}(\ker\pi_{R_0}/(\ker\pi_{R_0})^2)+\ell_{\mathcal O}(\mathcal O/(\pi_T\Delta))$. Then $\varphi'$ is bijective, $T'$ is isomorphic as an $\mathcal O$-algebra to a quotient $\mathcal O[[X_1,\dots,X_n]]/(f_1,\dots,f_n)$ by $n$ power series for some $n$, and $M'$ is free over $T'$.
--
--   This is the level-change form of Wiles' numerical criterion: the congruence-module inequality is assumed only at an auxiliary level $(T,M,R_0)$, and an adjoint pair $(i,j)$ with $j\circ i=\Delta$ propagates it to the level $(T',M',R')$, yielding there the complete intersection property of $T'$, the isomorphism $R'\cong T'$ and freeness of $M'$. It is the inductive step used in the Hecke-algebra application and in the construction of patching data for deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_bijective_and_free_of_length_le_of_levelChange.lean

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem AlgHom.bijective_and_free_of_length_le_of_levelChange
    {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {T : Type w} [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
    (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    {R₀ : Type v} [CommRing R₀] [Algebra 𝒪 R₀] (πR₀ : R₀ →ₐ[𝒪] 𝒪)
    (hS : (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR₀).Cotangent ≤
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)))
    {R' : Type v} [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    [IsAdicComplete (IsLocalRing.maximalIdeal R') R'] [Algebra 𝒪 R']
    {T' : Type w} [CommRing T'] [IsLocalRing T'] [Algebra 𝒪 T'] [Module.Finite 𝒪 T'] [Module.Free 𝒪 T']
    (φ' : R' →ₐ[𝒪] T') (hφ' : Function.Surjective φ') (πR' : R' →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪)
    (hπ' : πT'.comp φ' = πR') (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M' : Type x) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (hM' : Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ≠ ⊥)
    (hrank' : Module.finrank 𝒪 M' =
      Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) * Module.finrank 𝒪 T')
    (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))
    (Δ : T) (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
    (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)
    (hcot : Module.length 𝒪 (RingHom.ker πR').Cotangent ≤
      Module.length 𝒪 (RingHom.ker πR₀).Cotangent + Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ})) :
    Function.Bijective φ' ∧
      (∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T')) ∧
      Module.Free T' M' := by sorry
