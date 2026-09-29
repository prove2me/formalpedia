-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_pullbackMap_opens_of_forall_exists_le_isIso_pullbackMap_opens
-- name    : AlgebraicGeometry.isIso_pullbackMap_opens_of_forall_exists_le_isIso_pullbackMap_opens
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/820b7891-837c-581f-a707-111b6261207d
-- title:
--   Being an isomorphism over the base is local on the base
-- statement:
--   Let $X$, $Y$, $Z$ be schemes, let $p : Z \to Y$, $q : X \to Y$ and $h : Z \to X$ be morphisms with $h$ followed by $q$ equal to $p$, and let $U$ be an open subset of $Y$, regarded via its canonical open immersion $U.\iota : U \to Y$. For an open $W \le Y$ write $h_W$ for the morphism $\operatorname{pullback} p\, W.\iota \to \operatorname{pullback} q\, W.\iota$, i.e. $Z \times_Y W \to X \times_Y W$, obtained from the pair $(h, \mathrm{id}_W)$ over $\mathrm{id}_Y$ by the universal property of the fibre product (the two required commutativities coming from $h \mathbin{;} q = p$ and from the identity laws). The hypothesis is that every point $y \in U$ admits an open $V \le Y$ with $y \in V$, $V \le U$, and $h_V$ an isomorphism of schemes. The conclusion is that $h_U : Z \times_Y U \to X \times_Y U$ is an isomorphism. No hypotheses of finiteness, flatness, separatedness or properness are imposed on $p$, $q$ or $h$.
--
--   This is the statement that the property of $h$ being an isomorphism after base change to an open of $Y$ is local on $Y$: it upgrades local isomorphy over a neighbourhood of each point of $U$ to isomorphy over all of $U$. It is used in [`AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat`](thm.html#AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat), where an isomorphism on fibres is propagated to an isomorphism over an open neighbourhood.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_pullbackMap_opens_of_forall_exists_le_isIso_pullbackMap_opens.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_pullbackMap_opens_of_forall_exists_le_isIso_pullbackMap_opens
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (U : Y.Opens)
    (hU : ∀ y ∈ U, ∃ V : Y.Opens, y ∈ V ∧ V ≤ U ∧
      IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    IsIso (pullback.map p U.ι q U.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by sorry
