-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint
-- name    : AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/75bfa1b6-2ba8-5c92-916b-220dc1ba6254
-- title:
--   Birational morphism: stalk isomorphism at non-generic points over DVRs
-- statement:
--   Let $\Gamma$ and $G$ be schemes (in a fixed universe) which are integral, and let $\pi \colon \Gamma \to G$ be a morphism of schemes. Assume that the underlying continuous map of $\pi$ carries the generic point of $\Gamma$ to the generic point of $G$, and that the induced map of stalks $\pi^\sharp \colon \mathcal{O}_{G,\pi(\xi)} \to \mathcal{O}_{\Gamma,\xi}$ at the generic point $\xi$ of $\Gamma$ is an isomorphism; since the stalks at the generic points of integral schemes are the function fields, this is the condition that $\pi$ be birational. Let $\gamma$ be a point of $\Gamma$ distinct from the generic point of $\Gamma$, and assume that the local ring $\mathcal{O}_{G,\pi(\gamma)}$, the stalk of the structure sheaf of $G$ at the image point $\pi(\gamma)$, is a discrete valuation ring. The conclusion is that the stalk map $\pi^\sharp \colon \mathcal{O}_{G,\pi(\gamma)} \to \mathcal{O}_{\Gamma,\gamma}$ induced by $\pi$ at $\gamma$ is an isomorphism of (commutative) rings, i.e. an isomorphism in the relevant category of local rings.
--
--   This is the local form of the classical statement that a birational morphism of integral schemes is an isomorphism on local rings at points whose images have discrete valuation rings as local rings, the ring-theoretic heart being that no ring lies strictly between a discrete valuation ring and its fraction field. It is used in the scheme-theoretic groundwork on group schemes and Néron-type models, being cited by [`AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph`](thm.html#AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph) and by [`NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq`](thm.html#NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint
    {Γ G : Scheme.{u}} [IsIntegral Γ] [IsIntegral G] (π : Γ ⟶ G)
    (hgen : π.base (genericPoint Γ) = genericPoint G)
    (hbir : IsIso (π.stalkMap (genericPoint Γ)))
    (γ : Γ) (hγ : γ ≠ genericPoint Γ)
    [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))] :
    IsIso (π.stalkMap γ) := by sorry
