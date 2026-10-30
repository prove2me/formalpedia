-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_framed_disk_data
-- name    : ContactTopology.equivariant_legendrian_core_framed_disk_data
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T01:08:59.169437+00:00
-- url     : https://prove2.me/theorems/13e5b969-4f73-48dc-819b-d3a0abd32f5e
-- title:
--   Framed disk and signed push-off intersection for contactomorphic Legendrian cores
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere commuting with the antipodal involution. This theorem gives an explicit framed disk and a contact-framing push-off for the image of the real Legendrian core.
--
--   For $u\in\mathbb R^2$, put
--   $$D(u)=\frac{(2u_1,2u_2,1-|u|^2,0)}{1+|u|^2},\qquad G=F\circ D.$$
--   The map $G$ is globally smooth, sphere-valued, injective, and immersive. On the closed unit disk its antipodal identifications occur exactly between opposite boundary points. Its boundary is the supplied parametrized curve $F(u_1,u_2,0,0)$.
--
--   The standard contact plane has the explicit frame
--   $$A(y)=(-y_2,y_1,y_4,-y_3),\qquad B(y)=(y_4,-y_3,y_2,-y_1).$$
--   Pushing these vectors through $dF$ along $D$ gives smooth positive contact frames $U,V$ over the whole disk. They are tangent to the sphere, annihilated by its contact form, linearly independent, and span the contact plane at $G(u)$. On the boundary the actual circle tangent is $U$, so its coordinates in this extending frame are constant. The inward disk derivative is the image of $(0,0,1,0)$; together with the image of $(0,0,0,-1)$ it is a positively oriented normal frame $N_1,N_2$.
--
--   For $c(t)=(\cos t,\sin t)$ the contact normal satisfies
--   $$V(c(t))=\cos(\pi/2-t)N_1(c(t))+\sin(\pi/2-t)N_2(c(t)).$$
--   Every continuous angle describing this normal in the displayed framing, even allowing a tangential component, changes by exactly $-2\pi$ over a full circle. Every continuous angle describing the boundary tangent in $U,V$ changes by zero. These assertions include uniqueness of the total angle changes, rather than only a chosen angle formula.
--
--   Define the actual push-off family
--   $$P_s(u)=\frac{1-s^2}{1+s^2}(u_1,u_2,0,0)+\frac{2s}{1+s^2}(0,0,u_2,-u_1),\qquad H_s=F\circ P_s.$$
--   Along the parameter circle this family is jointly smooth, sphere-valued, embedded and antipodally equivariant. It starts at the given boundary and has initial velocity $2V$. For $0<s<1$ it is negatively transverse, and for every nonzero $s$ it is disjoint from the original boundary.
--
--   At $s=1/2$ the complete intersection criterion, including the antipodal identification, is
--   $$G(v)=\pm H_{1/2}(u),\quad |v|\leq1,\quad |u|=1
--   \quad\Longleftrightarrow\quad
--   v=(0,1/3),\quad u=\pm(0,1).$$
--   This is an interior intersection. It is transverse and negative: the contact volume evaluated on the two positively ordered disk derivatives and the push-off circle tangent is strictly negative. Thus the certificate supplies one negative intersection downstairs, with both possible lifts of its circle parameter accounted for.
--
--   The interface records explicit disk, frame, angle and signed-intersection data. Integrating these data with definitions of rational knot invariants and the rational Legendrian classification remains a separate step. The formal statement uses explicit local let-bindings and existing sphere-contact definitions. Joint smoothness of $H$ is asserted at points on the parameter circle, matching the sphere-local smoothness assumptions on $F$.
-- source:
--   Explicit standard-sphere coordinate calculation implementing the contact framing, rational Seifert disk, and rotation/intersection data in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Section 2.5 (definitions of rational Thurston–Bennequin and rotation invariants), and the maximal-core input used in Proposition 3.5 and Section 4. Contact framing and transverse push-offs: Hansjörg Geiges, Contact Geometry, arXiv:math/0307242v2, https://arxiv.org/abs/math/0307242v2, proof outline of Theorem 3.20. The explicit disk, frame, angle and unique-intersection formulas and their transport under the actual supplied map are established in the attached proof. This statement is a coordinate certificate and does not assert the full classification or a formal definition of rational invariants.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_framed_disk_data
    (F : EquivariantSphereContactomorphism) :
    let D : Plane → Phase := fun u =>
      ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
        (1-planeNormSq u)/(1+planeNormSq u),0]
    let G : Plane → Phase := F.toFun ∘ D
    let A : Phase → Phase := fun y => ![-y 1,y 0,y 3,-y 2]
    let B : Phase → Phase := fun y => ![y 3,-y 2,y 1,-y 0]
    let P : Plane → Phase → Phase := fun u v => fderiv ℝ F.toFun (D u) v
    let U : Plane → Phase := fun u => P u (A (D u))
    let V : Plane → Phase := fun u => P u (B (D u))
    let T : Plane → Phase := fun u => fderiv ℝ G u (circleTangent u)
    let N₁ : Plane → Phase := fun u => P u ![0,0,1,0]
    let N₂ : Plane → Phase := fun u => P u ![0,0,0,-1]
    let c : ℝ → Plane := fun t => ![Real.cos t,Real.sin t]
    let β : ℝ → ℝ := fun t => Real.pi/2-t
    let vol : Phase → Phase → Phase → Phase → ℝ := fun y v w z =>
      2*(phaseRadialContact y v*phaseRadialContact w z-
        phaseRadialContact y w*phaseRadialContact v z+
        phaseRadialContact y z*phaseRadialContact v w)
    let H : ℝ → Plane → Phase := fun s u => F.toFun
      (((1-s^2)/(1+s^2)) • ![u 0,u 1,0,0]+
        (2*s/(1+s^2)) • B ![u 0,u 1,0,0])
    let v₀ : Plane := ![0,1/3]
    let u₀ : Plane := ![0,1]
    (ContDiff ℝ ∞ G ∧ (∀ u, G u ∈ unitThreeSphere) ∧ Injective G ∧
      (∀ u, Injective (fderiv ℝ G u)) ∧
      ∀ u v, planeNormSq u ≤ 1 → planeNormSq v ≤ 1 →
        (G u= -G v ↔ planeNormSq u=1 ∧ planeNormSq v=1 ∧ u= -v)) ∧
    (ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧ ∀ u,
      phaseDot (G u) (U u)=0 ∧ phaseDot (G u) (V u)=0 ∧
      phaseRadialContact (G u) (U u)=0 ∧ phaseRadialContact (G u) (V u)=0 ∧
      0 < phaseRadialContact (U u) (V u) ∧
      (∀ a b : ℝ, a • U u+b • V u=0 → a=0 ∧ b=0) ∧
      ∀ w : Phase, phaseDot (G u) w=0 → phaseRadialContact (G u) w=0 →
        ∃ a b : ℝ, w=a • U u+b • V u) ∧
    (∀ u ∈ unitCircle, G u=F.toFun ![u 0,u 1,0,0] ∧ T u=U u ∧
      fderiv ℝ G u (-u)=N₁ u ∧ 0 < vol (G u) (T u) (N₁ u) (N₂ u)) ∧
    (Continuous β ∧ β (2*Real.pi)-β 0= -2*Real.pi ∧
      ∀ t, V (c t)=Real.cos (β t) • N₁ (c t)+Real.sin (β t) • N₂ (c t)) ∧
    (∀ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 (2*Real.pi)) →
      (∀ t ∈ Icc 0 (2*Real.pi), ∃ a : ℝ,
        V (c t)=a • T (c t)+Real.cos (θ t) • N₁ (c t)+Real.sin (θ t) • N₂ (c t)) →
      θ (2*Real.pi)-θ 0= -2*Real.pi) ∧
    (∀ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 (2*Real.pi)) →
      (∀ t ∈ Icc 0 (2*Real.pi), T (c t)=
        Real.cos (θ t) • U (c t)+Real.sin (θ t) • V (c t)) →
      θ (2*Real.pi)-θ 0=0) ∧
    (∀ s : ℝ, ∀ u ∈ unitCircle,
      ContDiffAt ℝ ∞ (fun z : ℝ × Plane => H z.1 z.2) (s,u) ∧
      H s u ∈ unitThreeSphere ∧ H s (-u)= -H s u) ∧
    (∀ s : ℝ, InjOn (H s) unitCircle) ∧
    (∀ s : ℝ, 0 < s → s < 1 → ∀ u ∈ unitCircle,
      phaseRadialContact (H s u) (fderiv ℝ (H s) u (circleTangent u)) < 0) ∧
    (∀ u ∈ unitCircle, H 0 u=G u ∧
      HasDerivAt (fun s : ℝ => H s u) ((2:ℝ) • V u) 0) ∧
    (∀ s : ℝ, s ≠ 0 → ∀ u ∈ unitCircle, ∀ v ∈ unitCircle, H s u ≠ G v) ∧
    (planeNormSq v₀ < 1 ∧ ∀ u v : Plane, u ∈ unitCircle → planeNormSq v ≤ 1 →
      ((G v=H (1/2) u ∨ G v= -H (1/2) u) ↔
        v=v₀ ∧ (u=u₀ ∨ u= -u₀))) ∧
    vol (G v₀) (fderiv ℝ G v₀ ![1,0]) (fderiv ℝ G v₀ ![0,1])
      (fderiv ℝ (H (1/2)) u₀ (circleTangent u₀)) < 0 := by sorry
