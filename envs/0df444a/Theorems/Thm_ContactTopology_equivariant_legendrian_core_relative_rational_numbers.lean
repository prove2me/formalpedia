-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_relative_rational_numbers
-- name    : ContactTopology.equivariant_legendrian_core_relative_rational_numbers
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T18:52:34.420258+00:00
-- url     : https://prove2.me/theorems/996ee4f2-7898-419e-94a6-95029fbfa6db
-- title:
--   Relative rational framing count and rotation of contactomorphic Legendrian cores
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard three-sphere commuting with the antipodal involution. Use the explicit disk and contact-normal push-off
--   $$D(u)=\frac{(2u_1,2u_2,1-|u|^2,0)}{1+|u|^2},\qquad G=F\circ D,$$
--   $$P_s(u)=\frac{1-s^2}{1+s^2}(u_1,u_2,0,0)+\frac{2s}{1+s^2}(0,0,u_2,-u_1),\qquad \gamma=F\circ P_{1/2}.$$
--   The contact planes have their fixed positive standard frame
--   $$A(y)=(-y_2,y_1,y_4,-y_3),\qquad B(y)=(y_4,-y_3,y_2,-y_1).$$
--
--   The closed-disk intersection parameters in the antipodal quotient form precisely the singleton $\{(0,1/3)\}$. Every matching circle parameter, with its tangent transported by the appropriate deck sign, gives intersection sign $-1$. Thus the sign is independent of the representative chosen at this intersection, and
--   $$G\cdot\gamma=-1,\qquad \frac{G\cdot\gamma}{2}=-\frac12.$$
--   The denominator is the positive double boundary-covering multiplicity of this explicit rational disk, established separately.
--
--   Let $u(t)=(\cos t,\sin t)$ and $T(t)=dG_{u(t)}(Ju(t))$. Express this actual boundary tangent in the fixed standard contact frame at $G(u(t))$ and form its complex coordinate
--   $$z(t)=\langle A(G(u(t))),T(t)\rangle+i\langle B(G(u(t))),T(t)\rangle.$$
--   This coordinate never vanishes. Its normalized direction has rational rotation zero with boundary multiplicity two. More precisely, the angular-lift rotation predicate holds for a rational number $q$ if and only if $q=0$.
--
--   These are relative classical-number calculations for the specified rational disk, contact-framing push-off and fixed extending contact frame. The statement uses a finite oriented-intersection functional and a continuous-angular-lift definition of winding. Independence under arbitrary changes of disk, push-off or contact trivialization, global maximality, and Legendrian classification are separate results.
-- source:
--   Kenneth L. Baker and John B. Etnyre, Rational linking and contact geometry, corrected version, https://etnyre.math.gatech.edu/preprints/papers/ratlink.pdf, Section 1, pp. 2–3 (normalized oriented intersections) and Section 1.2, pp. 4–5 (contact framing and rational rotation). Hyunki Min, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Section 2.5 and the maximal-core data in Theorem 1.5 for L(2,1). The explicit count, representative-sign independence and canonical-frame winding are supplied by the attached proof; general invariance, maximality and classification are not assumed or asserted.

import Definitions.Def_ContactTopology_RelativeRationalInvariants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open BirkhoffGlobalSection ContactTopology.RationalInvariants Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_relative_rational_numbers
    (F : EquivariantSphereContactomorphism) :
    let D : Plane → Phase := fun u =>
      ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
        (1-planeNormSq u)/(1+planeNormSq u),0]
    let G : Plane → Phase := F.toFun ∘ D
    let A : Phase → Phase := fun y => ![-y 1,y 0,y 3,-y 2]
    let B : Phase → Phase := fun y => ![y 3,-y 2,y 1,-y 0]
    let P : ℝ → Plane → Phase := fun s u =>
      ((1-s^2)/(1+s^2)) • ![u 0,u 1,0,0]+(2*s/(1+s^2)) • B ![u 0,u 1,0,0]
    let γ : Plane → Phase := F.toFun ∘ P (1/2)
    let c : ℝ → Plane := fun t => ![Real.cos t,Real.sin t]
    let z : ℝ → ℂ := fun t =>
      ⟨phaseDot (A (G (c t))) (fderiv ℝ G (c t) (circleTangent (c t))),
        phaseDot (B (G (c t))) (fderiv ℝ G (c t) (circleTangent (c t)))⟩
    quotientIntersectionSet G γ={![0,1/3]} ∧
    (∀ v u : Plane, v ∈ quotientIntersectionSet G γ → u ∈ unitCircle →
      (G v=γ u ∨ G v= -γ u) → representativeSign G γ v u= -1) ∧
    (quotientIntersectionSet G γ).Finite ∧
    (∀ h : (quotientIntersectionSet G γ).Finite,
      algebraicIntersection G γ h= -1 ∧ normalizedIntersection G γ 2 h= -1/2) ∧
    (∀ t : ℝ, z t ≠ 0) ∧
    (∀ q : ℚ, HasRationalRotation (fun t => direction (z t)) 2 q ↔ q=0) := by sorry
