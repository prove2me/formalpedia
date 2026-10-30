-- Prove2me | Theorems.Thm_ContactTopology_sphere_legendrian_core_coordinate_deformation
-- name    : ContactTopology.sphere_legendrian_core_coordinate_deformation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:01:11.831418+00:00
-- url     : https://prove2.me/theorems/cf4da317-5a6a-4e7c-8177-8c00a86b673e
-- title:
--   Coordinate contact deformation near a fixed real Legendrian circle
-- statement:
--   Let $F$ be a coorientation-preserving contactomorphism of the standard three-sphere commuting with the antipodal involution. Suppose $F$ fixes the real Legendrian circle pointwise. There is a positive uniform normal-strip width and a jointly smooth family of coordinate maps, starting at a lift of $F$ and ending at the identity. Every slice on the unit time interval is injective on that strip and pulls $dz-y\,dx$ back to a positive multiple of itself. The family fixes the core pointwise and commutes with longitudinal translation by one half, which represents the antipodal action.
--
--   The coordinate cover is explicit. With $\theta=2\pi x$, set
--   $$P(x,y,z)=\left(\cos\theta,\sin\theta,-2z\cos\theta+\frac{y}{2\pi}\sin\theta,-2z\sin\theta-\frac{y}{2\pi}\cos\theta\right),\qquad \chi=N\circ P.$$
--   Here $N$ is radial normalization. The initial coordinate map satisfies $\chi\circ H_0=F\circ\chi$ on the entire uniform strip, and $H_1=\mathrm{id}$.
--
--   This is the coordinate deformation used in the contact neighborhood-fixing argument. It does not assert an ambient contact isotopy of the whole sphere; extending the local isotopy is a separate step.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, Lemma 2.7(2), printed pp. 10–12, equations (2)–(8): coordinate rescaling and linear core deformation. https://arxiv.org/abs/2207.03590v2 . The explicit standard-sphere coordinate cover and construction of the lift from the actual sphere contactomorphism are supplied in this formalization; the conclusion is the coordinate step, not the full ambient extension lemma.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open scoped ContDiff

theorem ContactTopology.sphere_legendrian_core_coordinate_deformation (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ,
      F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) :
    let chart : (Fin 3 → ℝ) → BirkhoffGlobalSection.Phase := fun p =>
      BirkhoffGlobalSection.radialNormalize
        ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
          (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]
    let alpha : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun p v => v 2-p 1*v 0
    ∃ e : ℝ, 0 < e ∧ ∃ H : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => H q.1 q.2) ∧ H 1 = id ∧
      (∀ s x, H s ![x,0,0] = ![x,0,0]) ∧
      (∀ s p, H s (p+![1/2,0,0]) = H s p+![1/2,0,0]) ∧
      (∀ p, |p 1| < e ∧ |p 2| < e → chart (H 0 p) = F.toFun (chart p)) ∧
      ∀ s ∈ Set.Icc (0:ℝ) 1,
        Set.InjOn (H s) {p | |p 1| < e ∧ |p 2| < e} ∧
        ∀ p, |p 1| < e ∧ |p 2| < e → ∃ a : ℝ, 0 < a ∧ ∀ v,
          alpha (H s p) (fderiv ℝ (H s) p v) = a*alpha p v := by sorry
