-- Prove2me | Theorems.Thm_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension
-- name    : AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/be1daabd-0fc2-540b-b2b7-62bbbe58d3ba
-- title:
--   Constant field extension: regular differentials and correspondences
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$, $F'$ be $K$-algebras that are fields satisfying `IsCurveOver K F`, `IsCurveOver K F'` (every nonzero element has a degree-zero principal divisor, every place has residue field finite over $K$, and $\Omega[F/K]$ is free of rank $1$), each assumed finitely generated in the sense that some transcendental element $x$ has $F$ finite-dimensional over $K(x)$ (and likewise for $F'$). Let $\varphi,\psi\colon F\to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral; `Differential.correspondence φ ψ` is the $K$-linear endomorphism $\mathrm{tr}_\varphi\circ\psi^{*}$ of $\Omega[F/K]$. Let $E$ be an algebraically closed extension of $K$ and let $FE$, $F'E$ be fields over $E$, compatibly algebras over $F$, resp. $F'$, and over $K$, each satisfying the same curve and finite-generation hypotheses over $E$, with $FE$ generated over $E$ by the image of $F$ and $F'E$ generated over $E$ by the image of $F'$; let $\varphi_E,\psi_E\colon FE\to F'E$ be integral $E$-algebra maps extending $\varphi,\psi$. Writing $\kappa=$ `KaehlerDifferential.map K E F FE`, the conclusion asserts: $\kappa\circ\mathrm{correspondence}(\varphi,\psi)=\mathrm{correspondence}(\varphi_E,\psi_E)\circ\kappa$ on $\Omega[F/K]$; $\kappa$ is injective; $\kappa$ carries `regularDifferentials K F` into `regularDifferentials E FE`; and every element of `regularDifferentials E FE` lies in the $E$-span of $\kappa(\mathrm{regularDifferentials}\,K\,F)$.
--
--   This is the statement that differentials of the first kind commute with extension of an algebraically closed constant field, $H^0(X_E,\Omega^1)=H^0(X,\Omega^1)\otimes_K E$, equivariantly for the action of a correspondence on differentials. It is used in the study of the cotangent action of correspondences on $\mathrm{Pic}^0$, where it feeds into [`AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`](thm.html#AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [SMulCommClass E F FE] [IsAlgClosed E]
    [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral) :
    (∀ ω : Ω[F⁄K], KaehlerDifferential.map K E F FE (Differential.correspondence φ ψ ω) =
        Differential.correspondence φE ψE (KaehlerDifferential.map K E F FE ω)) ∧
    Function.Injective (KaehlerDifferential.map K E F FE) ∧
    (∀ ω ∈ regularDifferentials K F,
        KaehlerDifferential.map K E F FE ω ∈ regularDifferentials E FE) ∧
    (∀ η ∈ regularDifferentials E FE,
        η ∈ Submodule.span E
          (KaehlerDifferential.map K E F FE '' (regularDifferentials K F : Set (Ω[F⁄K])))) := by sorry
