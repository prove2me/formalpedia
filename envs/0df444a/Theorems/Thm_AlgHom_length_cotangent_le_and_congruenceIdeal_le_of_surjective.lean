-- Prove2me | Theorems.Thm_AlgHom_length_cotangent_le_and_congruenceIdeal_le_of_surjective
-- name    : AlgHom.length_cotangent_le_and_congruenceIdeal_le_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/11effe08-27c5-5d42-9edc-05060b94d6fd
-- title:
--   Monotonicity of cotangent length and congruence ideal under surjections
-- statement:
--   Let $\mathcal{O}$, $R$, $T$ be commutative rings with $R$ and $T$ commutative $\mathcal{O}$-algebras. Let $\varphi\colon R \to T$ be an $\mathcal{O}$-algebra homomorphism which is surjective as a function, and let $\pi_R\colon R \to \mathcal{O}$ and $\pi_T\colon T \to \mathcal{O}$ be $\mathcal{O}$-algebra homomorphisms (augmentations) such that $\pi_T \circ \varphi = \pi_R$. Write $I_R = \ker \pi_R$ and $I_T = \ker \pi_T$ for the corresponding ideals, and for an ideal $I$ let $I_{\mathrm{Cotangent}} = I/I^2$ denote its cotangent module, regarded as an $\mathcal{O}$-module. The conclusion is the conjunction of two assertions: first, the $\mathcal{O}$-module length of $I_T/I_T^2$ is at most the $\mathcal{O}$-module length of $I_R/I_R^2$ (lengths taken in the extended sense, so the inequality is one of values in $\mathbb{N}\cup\{\infty\}$); second, the image under $\pi_R$ of the annihilator of $I_R$ (as a submodule of $R$) is contained in the image under $\pi_T$ of the annihilator of $I_T$, as ideals of $\mathcal{O}$.
--
--   In the notation of the Wiles–Lenstra numerical criterion, with $\Phi_\pi = I/I^2$ and congruence ideal $\eta_\pi = \pi(\operatorname{Ann} I)$, this is the monotonicity remark that a surjection of augmented $\mathcal{O}$-algebras forces $\operatorname{length} \Phi_T \le \operatorname{length} \Phi_R$ and $\eta_R \subseteq \eta_T$. It is invoked when passing from a deformation ring to a Hecke algebra in the construction of algebra homomorphisms with bounded cotangent length for residually modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_length_cotangent_le_and_congruenceIdeal_le_of_surjective.lean

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem AlgHom.length_cotangent_le_and_congruenceIdeal_le_of_surjective
    {𝒪 : Type u} {R : Type v} {T : Type w} [CommRing 𝒪]
    [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) :
    Module.length 𝒪 (RingHom.ker πT).Cotangent ≤ Module.length 𝒪 (RingHom.ker πR).Cotangent ∧
      (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πT).annihilator.map πT := by sorry
