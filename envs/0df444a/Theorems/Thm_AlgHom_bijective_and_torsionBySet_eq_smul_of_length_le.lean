-- Prove2me | Theorems.Thm_AlgHom_bijective_and_torsionBySet_eq_smul_of_length_le
-- name    : AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/34dad047-7963-5e3d-b12e-fb9e50a532b2
-- title:
--   Numerical criterion with a Hecke module: R=T and M[wp]=IM
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a domain, discrete valuation ring, adically complete for its maximal ideal), $R$ a noetherian local $\mathcal O$-algebra adically complete for its maximal ideal, and $T$ a local $\mathcal O$-algebra which is finite and free as an $\mathcal O$-module. Let $\varphi : R \to T$ be a surjective $\mathcal O$-algebra map and $\pi_R : R \to \mathcal O$, $\pi_T : T \to \mathcal O$ $\mathcal O$-algebra maps with $\pi_T \circ \varphi = \pi_R$; write $\wp = \ker \pi_T$ and $I = \operatorname{Ann}_T(\wp)$, and assume the ideal $\pi_T(I) \subseteq \mathcal O$ is nonzero. Let $M$ be a $T$-module, also an $\mathcal O$-module compatibly via the scalar tower, finite and free over $\mathcal O$, with $M[\wp] := \{m : \wp \cdot m = 0\}$ nonzero, and assume the inequality in $\mathbb N \cup \{\infty\}$
--   $$\operatorname{rank}_{\mathcal O} M[\wp] \cdot \operatorname{length}_{\mathcal O}\bigl(\ker \pi_R / (\ker \pi_R)^2\bigr) \le \operatorname{length}_{\mathcal O}\bigl(M / (M[\wp] + M[I])\bigr),$$
--   where the cotangent module is that of the ideal $\ker\pi_R$ and $M[I]$ is the $I$-torsion of $M$. Then $\varphi$ is bijective; there are an $n \in \mathbb N$ and $f_1,\dots,f_n \in \mathcal O[[x_1,\dots,x_n]]$ together with an $\mathcal O$-algebra isomorphism $\mathcal O[[x_1,\dots,x_n]]/(f_1,\dots,f_n) \simeq T$; and $M[\wp] = I \cdot M$.
--
--   This is the numerical criterion of Wiles–Lenstra type in the form carrying a Hecke-module variable $M$: the inequality of an $\mathcal O$-length of the cotangent module of $\ker\pi_R$ against a length attached to $M$ forces simultaneously that $\varphi$ is an isomorphism, that $T$ is a complete intersection over $\mathcal O$, and that the $\wp$-torsion of $M$ equals $IM$. It is stated purely in commutative-algebra terms and is used on the non-minimal $R = T$ route, being cited by [`AlgHom.bijective_and_free_of_length_le`](thm.html#AlgHom.bijective_and_free_of_length_le), where the conclusion $M[\wp] = IM$ is upgraded to freeness of $M$ over $T$ with further rank and duality input; the numerical hypotheses alone do not give freeness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_bijective_and_torsionBySet_eq_smul_of_length_le.lean

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

theorem AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le
    {𝒪 : Type u} {R : Type v} {T : Type w}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra 𝒪 R]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (hM : Submodule.torsionBySet T M ↑(RingHom.ker πT) ≠ ⊥)
    (hle : (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator))) :
    Function.Bijective φ ∧
      (∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) ∧
      Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤ := by sorry
