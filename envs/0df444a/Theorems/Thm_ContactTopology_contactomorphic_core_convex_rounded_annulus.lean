-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_convex_rounded_annulus
-- name    : ContactTopology.contactomorphic_core_convex_rounded_annulus
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:48:44.036992+00:00
-- url     : https://prove2.me/theorems/f8fcac31-c1c1-4354-853d-30cd95a9c50e
-- title:
--   A convex rounded annulus around the actual contactomorphic Legendrian core
-- statement:
--   Let $F$ be an antipodally equivariant coorientation-preserving contactomorphism of the standard contact three-sphere, and let $r>0$. Construct a rounded annulus in an actual rotating contact collar of the image Legendrian core, together with an actual transverse contact vector field on a sphere neighborhood.
--
--   More precisely, there are a constant $c>0$, a globally smooth sphere-valued contact cover $C:\mathbb R^3\to S^3$, a smooth positive factor $L$, and a globally smooth surface parametrization $S:\mathbb R^2\to S^3$ with
--   $$C^*\lambda=L\bigl(\sin(4\pi z)\,dx+\cos(4\pi z)\,dy\bigr),\qquad
--   C(0,0,z)=F(\cos(2\pi z),\sin(2\pi z),0,0).$$
--   Both derivatives are injective. The surface has exactly the integer longitudinal fibers:
--   $$S(s,z)=S(t,w)\quad\Longleftrightarrow\quad s=t\ \text{and}\ z-w\in\mathbb Z,$$
--   and its half-period is antipodal. On the two outer regions it agrees with the original collar faces:
--   $$S(s,z)=C(0,r(c-s),z)\quad(s\le0),\qquad
--   S(s,z)=C(r(c+s-1),0,z)\quad(s\ge1).$$
--   Consequently the joins are smooth to all orders. The image of the compact rectangle $[0,1]^2$ is compact and equals the image of $[0,1]\times\mathbb R$, giving the compact periodically parametrized annulus. Longitudinal rulings are Legendrian.
--
--   There are an open ambient set $O$ containing the surface and a vector field $Y$ smooth at every sphere point in $O$. There it is tangent to the sphere, commutes with the antipodal action, and satisfies the contact vector-field identity
--   $$\lambda_{Y(y)}(w)+\lambda_y(DY_y w)=a(y)\lambda_y(w)\qquad(w\in T_yS^3),$$
--   where the first term denotes the same bilinear radial contact pairing as in the definition of $\lambda$. At every parameter point, $Y(S(p))$ lies outside the image of $DS_p$. This is an actual constructed transverse contact field, not an assumed compatibility condition.
--
--   The dividing locus is exactly the union of smooth regular branches
--   $$z=\frac{k}{4}-\frac{\psi(s)}{4\pi},\qquad k\in\mathbb Z,\qquad
--   \psi(0)=0,\quad\psi(1)=\frac\pi2.$$
--   The corresponding sphere curves connect $C(0,rc,k/4)$ to $C(rc,0,k/4-1/8)$.
--
--   This is the twice-rotating sphere-core instance of Honda's local edge-rounding construction. The formal statement uses an explicit periodic parametrization and exact fibers, rather than a separately defined quotient-manifold annulus. Its boundary longitudinal circles are included among the Legendrian rulings. It asserts neither an arbitrary-manifold gluing theorem, a bypass construction, a generic convex movie, tight solid-torus core uniqueness, nor the full core-isotopy classification.
-- source:
--   Ko Honda, Gluing tight contact structures, https://arxiv.org/pdf/math/0102029, Section 1.5, p.11, edge-rounding paragraph and dividing shift -1/(4n); convexity definition in Section 1.1, p.2. Derived explicit n=2 construction in the actual equivariant sphere-core collar, using a normalized symplectic shear and transported contact Euler field. Not the arbitrary-manifold gluing statement.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.IntermediateValue
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology

theorem ContactTopology.contactomorphic_core_convex_rounded_annulus
    (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, ∃ C : (Fin 3 → ℝ) → Phase, ∃ L : (Fin 3 → ℝ) → ℝ,
    ∃ S : ℝ × ℝ → Phase, ∃ Y : Phase → Phase, ∃ O : Set Phase,
    ∃ phase : ℝ → ℝ, ∃ γ : ℤ → ℝ → Phase,
      0 < c ∧ ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ L ∧ (∀ y, 0 < L y) ∧
      (∀ y, C y ∈ unitThreeSphere) ∧ (∀ y, Injective (fderiv ℝ C y)) ∧
      (∀ z, C ![0,0,z]=F.toFun ![Real.cos (2*Real.pi*z),Real.sin (2*Real.pi*z),0,0]) ∧
      (∀ y v, phaseRadialContact (C y) (fderiv ℝ C y v)=
        L y*(Real.sin (4*Real.pi*y 2)*v 0+Real.cos (4*Real.pi*y 2)*v 1)) ∧
      ContDiff ℝ ∞ S ∧ (∀ p, S p ∈ unitThreeSphere) ∧
      (∀ p, Injective (fderiv ℝ S p)) ∧
      (∀ p q, S p=S q ↔ p.1=q.1 ∧ ∃ k : ℤ, p.2=q.2+k) ∧
      (∀ s z, S (s,z+1/2)= -S (s,z)) ∧
      (∀ s z, s ≤ 0 → S (s,z)=C ![0,r*(c-s),z]) ∧
      (∀ s z, 1 ≤ s → S (s,z)=C ![r*(c+s-1),0,z]) ∧
      IsCompact (S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) ∧
      (∀ y, y ∈ S '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ↔
        ∃ s ∈ Icc (0:ℝ) 1, ∃ z : ℝ, y=S (s,z)) ∧
      IsOpen O ∧ range S ⊆ O ∧
      (∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ Y y ∧ phaseDot y (Y y)=0 ∧
        Y (-y)= -Y y ∧ ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
          phaseRadialContact (Y y) w+phaseRadialContact y (fderiv ℝ Y y w)=a*phaseRadialContact y w) ∧
      (∀ p v : ℝ × ℝ, Y (S p) ≠ fderiv ℝ S p v) ∧
      (∀ p : ℝ × ℝ, phaseRadialContact (S p) (fderiv ℝ S p (0,1))=0) ∧
      ContDiff ℝ ∞ phase ∧ phase 0=0 ∧ phase 1=Real.pi/2 ∧
      (∀ k, ContDiff ℝ ∞ (γ k)) ∧
      (∀ k s, γ k s=S (s,(k:ℝ)/4-phase s/(4*Real.pi))) ∧
      (∀ k s, deriv (γ k) s ≠ 0) ∧
      (∀ k, γ k 0=C ![0,r*c,(k:ℝ)/4] ∧ γ k 1=C ![r*c,0,(k:ℝ)/4-1/8]) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ z : ℝ,
        (phaseRadialContact (S (s,z)) (Y (S (s,z)))=0 ↔
          ∃ k : ℤ, z=(k:ℝ)/4-phase s/(4*Real.pi)) := by sorry
