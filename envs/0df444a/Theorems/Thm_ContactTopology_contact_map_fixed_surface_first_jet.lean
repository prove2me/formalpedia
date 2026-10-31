-- Prove2me | Theorems.Thm_ContactTopology_contact_map_fixed_surface_first_jet
-- name    : ContactTopology.contact_map_fixed_surface_first_jet
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:01:02.460552+00:00
-- url     : https://prove2.me/theorems/22c01c4c-e236-4d7f-b44f-124b6bf8940a
-- title:
--   Derivative constraints for a contact map fixing a surface
-- statement:
--   Let $\alpha=a_0\,dx+a_1\,dy+a_2\,dz$ be a smooth one-form on $\mathbb R^3$, and let $O$ be open. Suppose smooth maps $F:O\to\mathbb R^3$ and $L:O\to\mathbb R$ satisfy
--   $$
--   F^*\alpha=L\alpha,
--   \qquad F(x,y,0)=(x,y,0)\quad\text{wherever }(x,y,0)\in O.
--   $$
--   At a point $p\in O\cap\{z=0\}$ where $\alpha$ is contact, equivalently $a(p)\cdot\operatorname{curl}a(p)\ne0$, the actual multiplier and derivative obey
--   $$
--   L(p)=1,\qquad
--   DF_p e_x=e_x,\qquad DF_p e_y=e_y,\qquad
--   DF_p e_z=(b_0,b_1,1),\qquad
--   a_0(p)b_0+a_1(p)b_1=0.
--   $$
--   Thus the normal component of the pushed-forward normal is exactly one, and any remaining shear lies in the characteristic direction of the fixed surface. The theorem does not assert that the entire derivative is the identity.
--
--   The contact identity and surface-fixing hypotheses are local to $O$. No inverse map, positive multiplier assumption or pre-existing transverse-field certificate is needed for this derivative conclusion. This is a local analytic input to convex-surface neighborhood fixing, as used in Min's Lemma 2.7(1) and the later bypass comparison. It does not assert an ambient neighborhood-fixing isotopy or the global Legendrian core classification.
-- source:
--   Local first-derivative calculation for the transverse-field interpolation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma 2.7(1), printed pp. 10–11. The explicit arbitrary-one-form pointwise derivative statement, including characteristic singularities and the allowed characteristic shear, is derived here and is not stated verbatim in the source. Uses naturality of the exterior pairing. This is a prerequisite, not a proof of neighborhood fixing or the full core classification.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.contact_map_fixed_surface_first_jet
    (a F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (L : (Fin 3 → ℝ) → ℝ)
    (O : Set (Fin 3 → ℝ)) (hO : IsOpen O)
    (ha : ContDiff ℝ ∞ a) (hF : ContDiffOn ℝ ∞ F O) (hL : ContDiffOn ℝ ∞ L O)
    (hfix : ∀ z ∈ O, z 2=0 → F z=z)
    (y : Fin 3 → ℝ) (hy : y ∈ O) (hy0 : y 2=0) :
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun p v => p 0*v 0+p 1*v 1+p 2*v 2
    let c : (Fin 3 → ℝ) :=
      ![fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1,
        fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2,
        fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0]
    (∀ z ∈ O, ∀ v, B (a (F z)) (fderiv ℝ F z v)=L z*B (a z) v) →
    B (a y) c ≠ 0 →
      L y=1 ∧ fderiv ℝ F y (Pi.single 0 1)=Pi.single 0 1 ∧
      fderiv ℝ F y (Pi.single 1 1)=Pi.single 1 1 ∧
      fderiv ℝ F y (Pi.single 2 1) 2=1 ∧
      a y 0*fderiv ℝ F y (Pi.single 2 1) 0+a y 1*fderiv ℝ F y (Pi.single 2 1) 1=0 := by sorry
