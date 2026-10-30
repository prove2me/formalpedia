-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_convex_boundary_data
-- name    : ContactTopology.equivariant_legendrian_convex_boundary_data
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T00:43:14.953647+00:00
-- url     : https://prove2.me/theorems/eb4e25e9-a757-4417-ba8c-02ea0cff9da1
-- title:
--   Explicit convex boundary data for contactomorphic Legendrian cores
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere commuting with the antipodal involution, and let $r>0$. Use the explicit contact coordinate cover $\chi(x,y,z)$ of the real Legendrian core, with $x\sim x+1$, normal coordinates $y,z$, and positive pullback of the standard radial contact form proportional to $dz-y\,dx$. Put $G=F\circ\chi$ and
--   $$T_r=\{G(x,y,z):y^2+z^2=r^2\}.$$
--   The map $G$ is smooth, sphere-valued and an immersion, and its only fibers are integer shifts of the longitudinal coordinate. The set $T_r$ is compact.
--
--   Define the sphere-tangent fiber-dilation field and its image under $F$ by
--   $$X(q,p)=(0,p)-|p|^2(q,p),\qquad Y(F(v))=dF_v(X(v)).$$
--   There is a single ambient open neighborhood $O$ of $T_r$ on which, restricted to the sphere, $Y$ is smooth, tangent and an infinitesimal contact transformation. An explicit smooth normal-radius function $R$, obtained from the inverse contact coordinates and $F^{-1}$, has
--   $$T_r=O\cap S^3\cap R^{-1}(r^2),\qquad dR_y(Y_y)>0\quad(y\in T_r).$$
--   Thus $Y$ is transverse to this regular boundary. Its dividing set is precisely
--   $$\{y\in T_r:\lambda_y(Y_y)=0\}=C_r\;\dot\cup\; C_{-r},\qquad C_s=\{G(x,s,0):x\in\mathbb R\}.$$
--   Each parametrized curve is smooth and regular, its image is compact and connected, equality of parameter values occurs exactly modulo integers, and translation by $1/2$ is the antipodal action. The two displayed curves are disjoint.
--
--   This gives explicit convex-neighborhood boundary data for the actual image of a Legendrian core under $F$. It supplies the standard-neighborhood geometry used in rational Legendrian classification. It does not assert a knot-classification or tight-solid-torus uniqueness theorem.
--
--   **Formalization Note.** The displayed coordinate cover, vector field and normal-radius functions are written explicitly as local let-bindings in the statement. No unproved geometric predicates or unpublished custom definitions are part of the interface.
-- source:
--   Explicit standard-sphere coordinate specialization of the standard Legendrian neighborhood in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Lemma 2.7(2), printed pp. 10–12, and the standard-neighborhood boundary data used in Lemma 3.4 and Proposition 3.5, printed pp. 30–32. Convex-surface convention: Min Section 2.1, and Hansjörg Geiges, Contact geometry, arXiv:math/0307242v2, https://arxiv.org/abs/math/0307242v2, Section 2.4.5 and the Legendrian neighborhood model in Example 2.29 (printed p. 21). The explicit fiber-Euler field, defining function, transported contact identity and two-curve calculation are supplied in the attached proof.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_convex_boundary_data
    (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    let chart : (Fin 3 → ℝ) → Phase := fun p => radialNormalize
      ![Real.cos (2*Real.pi*p 0),Real.sin (2*Real.pi*p 0),
        (-2*p 2)*Real.cos (2*Real.pi*p 0)+(p 1/(2*Real.pi))*Real.sin (2*Real.pi*p 0),
        (-2*p 2)*Real.sin (2*Real.pi*p 0)-(p 1/(2*Real.pi))*Real.cos (2*Real.pi*p 0)]
    let G : (Fin 3 → ℝ) → Phase := fun p => F.toFun (chart p)
    let X : Phase → Phase := fun y => ![0,0,y 2,y 3]-wNormSq y • y
    let Y : Phase → Phase := fun y => fderiv ℝ F.toFun (F.invFun y) (X (F.invFun y))
    let N₁ : Phase → ℝ := fun y => -2*Real.pi*(y 0*y 3-y 1*y 2)/zNormSq y
    let N₂ : Phase → ℝ := fun y => -(y 0*y 2+y 1*y 3)/(2*zNormSq y)
    let R : Phase → ℝ := fun y => N₁ (F.invFun y)^2+N₂ (F.invFun y)^2
    let T : Set Phase := G '' {p | p 1^2+p 2^2=r^2}
    let C : ℝ → ℝ → Phase := fun s x => G ![x,s,0]
    ContDiff ℝ ∞ G ∧ (∀ p, G p ∈ unitThreeSphere) ∧
      (∀ p, Injective (fderiv ℝ G p)) ∧
      (∀ p q, G p=G q ↔ ∃ n : ℤ, p=q+![(n:ℝ),0,0]) ∧ IsCompact T ∧
      (∃ O : Set Phase, IsOpen O ∧ T ⊆ O ∧
        (O ∩ unitThreeSphere) ∩ {y | R y=r^2}=T ∧
        (∀ y ∈ O ∩ unitThreeSphere, ContDiffAt ℝ ∞ Y y ∧ phaseDot y (Y y)=0 ∧
          ∃ a : ℝ, ∀ w : Phase, phaseDot y w=0 →
            phaseRadialContact (Y y) w+phaseRadialContact y (fderiv ℝ Y y w)=a*phaseRadialContact y w) ∧
        ∀ y ∈ T, ContDiffAt ℝ ∞ R y ∧ 0 < fderiv ℝ R y (Y y)) ∧
      {y ∈ T | phaseRadialContact y (Y y)=0}=range (C r) ∪ range (C (-r)) ∧
      Disjoint (range (C r)) (range (C (-r))) ∧
      ∀ s : ℝ, ContDiff ℝ ∞ (C s) ∧ (∀ x, deriv (C s) x ≠ 0) ∧
        (∀ x y, C s x=C s y ↔ ∃ n : ℤ, x=y+n) ∧
        (∀ x, C s (x+1/2)= -C s x) ∧ IsCompact (range (C s)) ∧ IsConnected (range (C s)) := by sorry
