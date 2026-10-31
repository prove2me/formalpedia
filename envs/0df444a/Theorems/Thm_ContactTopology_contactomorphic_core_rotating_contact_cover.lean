-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_rotating_contact_cover
-- name    : ContactTopology.contactomorphic_core_rotating_contact_cover
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:35:54.349297+00:00
-- url     : https://prove2.me/theorems/5972b827-6889-4ca9-9bff-ed09715ed996
-- title:
--   A rotating contact collar cover of the actual contactomorphic Legendrian core
-- statement:
--   Let $F$ be an antipodally equivariant coorientation-preserving contactomorphism of the standard contact three-sphere, and let $n$ be a positive integer. There exist a globally smooth sphere-valued map $C:\mathbb R^3\to S^3$ and a smooth positive function $L$ such that
--   $$C^*\lambda=L\bigl(\sin(2\pi n z)\,dx+\cos(2\pi n z)\,dy\bigr).$$
--   The central line maps to the actual contactomorphic Legendrian core:
--   $$C(0,0,z)=F\bigl(\cos(2\pi z),\sin(2\pi z),0,0\bigr).$$
--   The derivative of $C$ is injective at every point, and its fibers are exactly the integer longitudinal translates:
--   $$C(x,y,z)=C(x',y',z')\quad\Longleftrightarrow\quad x=x',\ y=y',\ z-z'\in\mathbb Z.$$
--   For $n=2$ the half-period gives the antipodal map while keeping the two normal coordinates fixed:
--   $$C(x,y,z+\tfrac12)=-C(x,y,z).$$
--
--   At each source point, the theorem also constructs an actual inverse map smooth at its image. It has the pointwise inverse identity, a left inverse identity on a source neighborhood, and a right inverse identity on a sphere neighborhood. These are genuine local coordinates, rather than only an infinitesimal pullback formula. The supplied sphere contactomorphism is required smooth only at sphere points, as in its definition.
--
--   This constructs the rotating Legendrian collar model used for edge rounding around the actual core. It provides the contact factor, inverse coordinates, periodic fibers, and antipodal compatibility from the actual map $F$. Transport of a transverse rounding field to a geometric rounded neighborhood, quotient descent of the rounding, a bypass construction, and the generic convex movie remain separate tasks.
-- source:
--   Ko Honda, Gluing tight contact structures, https://arxiv.org/abs/math/0102029, Section 1.5, arXiv p.11, rotating Legendrian collar form used for edge rounding. Derived construction for the actual sphere core using the previously established jet contact cover, an explicit rotating coordinate change, and its inverse; not a verbatim arbitrary-manifold neighborhood theorem.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology

theorem ContactTopology.contactomorphic_core_rotating_contact_cover
    (F : EquivariantSphereContactomorphism) (n : ℕ) (hn : 0 < n) :
    ∃ C : (Fin 3 → ℝ) → Phase, ∃ L : (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ L ∧ (∀ y, 0 < L y) ∧
      (∀ y, C y ∈ unitThreeSphere) ∧
      (∀ z, C ![0,0,z]=F.toFun ![Real.cos (2*Real.pi*z),Real.sin (2*Real.pi*z),0,0]) ∧
      (∀ y, Injective (fderiv ℝ C y)) ∧
      (∀ y v, phaseRadialContact (C y) (fderiv ℝ C y v)=
        L y*(Real.sin (2*Real.pi*n*y 2)*v 0+Real.cos (2*Real.pi*n*y 2)*v 1)) ∧
      (∀ y z, C y=C z ↔ ∃ k : ℤ, y=![z 0,z 1,z 2+k]) ∧
      (n=2 → ∀ y, C ![y 0,y 1,y 2+1/2]= -C y) ∧
      ∀ y, ∃ R : Phase → (Fin 3 → ℝ), ContDiffAt ℝ ∞ R (C y) ∧ R (C y)=y ∧
        (∀ᶠ q in 𝓝 y, R (C q)=q) ∧
        ∀ᶠ z in 𝓝 (C y), z ∈ unitThreeSphere → C (R z)=z := by sorry
