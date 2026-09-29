-- Prove2me | Theorems.Thm_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural
-- name    : CategoryTheory.Sheaf.exists_iso_of_addEquiv_obj_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/e3aceaf3-b256-53ee-85b1-28c627de9a96
-- title:
--   Sheaf isomorphism from a natural family of additive bijections
-- statement:
--   Let $C$ be a category and $J$ a Grothendieck topology on $C$, and let $F$ and $G$ be sheaves on $(C,J)$ with values in the category of abelian groups. Suppose given, for every object $U$ of $C^{\mathrm{op}}$, an additive group isomorphism $e_U \colon F(U) \to G(U)$ between the groups of sections of the underlying presheaves, and suppose these are natural in the sense that for all $U, V$ in $C^{\mathrm{op}}$, every morphism $k \colon U \to V$ and every section $s \in F(U)$ one has $e_V(F(k)(s)) = G(k)(e_U(s))$, i.e. the $e_U$ commute with the restriction maps. The conclusion asserts the existence of an isomorphism $\varphi \colon F \cong G$ in the category of abelian-group-valued sheaves on $(C,J)$ whose forward direction realises the given family on sections: for every $U$ in $C^{\mathrm{op}}$ and every $s \in F(U)$, the component at $U$ of the underlying presheaf morphism of $\varphi.\mathrm{hom}$ sends $s$ to $e_U(s)$.
--
--   This is the standard transfer principle that a family of isomorphisms of sections, natural in the object, assembles into an isomorphism of sheaves of abelian groups, with the prescribed effect on sections. It is used to identify points sheaves arising from different but naturally identified descriptions, and is cited in the construction of a retraction of the kernel of a multiplication-by-$n$ map on a Hopf points sheaf attached to an idempotent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

theorem CategoryTheory.Sheaf.exists_iso_of_addEquiv_obj_natural
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F G : Sheaf J Ab.{w}) (e : ∀ U : Cᵒᵖ, F.obj.obj U ≃+ G.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (s : F.obj.obj U), e V (F.obj.map k s) = G.obj.map k (e U s)) :
    ∃ φ : F ≅ G, ∀ (U : Cᵒᵖ) (s : F.obj.obj U), φ.hom.hom.app U s = e U s := by sorry
