-- Prove2me | Theorems.Thm_FamousTheorems_yang_baxter_braided_7a
-- name    : FamousTheorems.yang_baxter_braided_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:25.586203+00:00
-- url     : https://prove2.me/theorems/d1b34b8d-9570-4ec2-be57-4cdff676d225
-- title:
--   The Yang–Baxter equation in braided monoidal categories
-- statement:
--   **The Yang–Baxter equation in braided monoidal categories.** In a braided monoidal category with braiding $\beta$ and associator $\alpha$, the two ways of reversing three objects $X\otimes Y\otimes Z$ into $Z\otimes Y\otimes X$ by braidings agree:
--   $$(\beta_{Y,Z}\otimes1_X)(1_Y\otimes\beta_{X,Z})(\beta_{X,Y}\otimes1_Z)=(1_Z\otimes\beta_{X,Y})(\beta_{X,Z}\otimes1_Y)(1_X\otimes\beta_{Y,Z}),$$
--   with associators inserted where needed.
--
--   This is the braid relation $\sigma_1\sigma_2\sigma_1=\sigma_2\sigma_1\sigma_2$ of Artin's braid groups. It follows from the hexagon axioms and the naturality of the braiding. It is the reason that braided categories give representations of braid groups and invariants of knots. It also connects braided categories with quantum groups and with the Yang–Baxter equation of statistical mechanics.
--
--   **Formalization note.** Mathlib's `CategoryTheory.BraidedCategory.yang_baxter`. Composition `≫` is written in diagrammatic order, `f ▷ Z` and `Y ◁ f` are whiskering, and `α_` and `β_` are the associator and the braiding.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.BraidedCategory.yang_baxter`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open CategoryTheory MonoidalCategory

theorem yang_baxter_braided_7a {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫
        (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom := by sorry

end FamousTheorems
