-- Prove2me | Theorems.Thm_AlgHom_bijective_and_free_of_length_le
-- name    : AlgHom.bijective_and_free_of_length_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/6f62f438-44bf-5874-9501-de742211d0c0
-- title:
--   Numerical criterion with pairing: R=T complete intersection, M free
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a noetherian local domain that is a discrete valuation ring and is adically complete for its maximal ideal), let $R$ be a noetherian local $\mathcal O$-algebra complete for its maximal-ideal-adic topology, and let $T$ be a local $\mathcal O$-algebra that is finite and free as an $\mathcal O$-module. Given a surjective $\mathcal O$-algebra map $\varphi : R \to T$ and augmentations $\pi_R : R \to \mathcal O$, $\pi_T : T \to \mathcal O$ with $\pi_T \circ \varphi = \pi_R$, assume $\eta := \pi_T(\operatorname{Ann}_T(\ker \pi_T)) \neq 0$. Let $M$ be a $T$-module, finite and free over $\mathcal O$ with compatible scalars, equipped with an $\mathcal O$-bilinear form $B : M \times M \to \mathcal O$ satisfying $B(tm,n) = B(m,tn)$ for all $t \in T$ and whose associated map $M \to \operatorname{Hom}_{\mathcal O}(M,\mathcal O)$ is bijective. Write $M[\wp]$ for the submodule of elements annihilated by every element of $\wp = \ker \pi_T$, and $M[I]$ for the submodule annihilated by every element of $I = \operatorname{Ann}_T(\wp)$. Assume $M[\wp] \neq 0$, that $\operatorname{rank}_{\mathcal O} M = \operatorname{rank}_{\mathcal O} M[\wp] \cdot \operatorname{rank}_{\mathcal O} T$, and the inequality in $\mathbb N_\infty$
--   $$\operatorname{rank}_{\mathcal O} M[\wp] \cdot \operatorname{length}_{\mathcal O} \bigl((\ker \pi_R)/(\ker \pi_R)^2\bigr) \le \operatorname{length}_{\mathcal O}\bigl(M/(M[\wp] + M[I])\bigr).$$
--   Then $\varphi$ is bijective; there are an $n \in \mathbb N$ and $n$ power series $f_1,\dots,f_n \in \mathcal O[[x_1,\dots,x_n]]$ such that $\mathcal O[[x_1,\dots,x_n]]/(f_1,\dots,f_n)$ is isomorphic to $T$ as an $\mathcal O$-algebra; and $M$ is free as a $T$-module.
--
--   This is the numerical criterion for $R = T$ in its module-theoretic form, with a self-duality datum on the Hecke-type module $M$ as input and freeness of $M$ over $T$ as additional output; $T$ is shown along the way to be a complete intersection over $\mathcal O$ of relative dimension zero. It is stated purely in commutative-algebra terms, no Galois representation or modular form entering, and is applied through [`AlgHom.bijective_and_free_of_length_le_of_levelChange`](thm.html#AlgHom.bijective_and_free_of_length_le_of_levelChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_bijective_and_free_of_length_le.lean

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

theorem AlgHom.bijective_and_free_of_length_le
    {𝒪 : Type u} {R : Type v} {T : Type w}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra 𝒪 R]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hM : Submodule.torsionBySet T M ↑(RingHom.ker πT) ≠ ⊥)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hle : (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator))) :
    Function.Bijective φ ∧
      (∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) ∧
      Module.Free T M := by sorry
