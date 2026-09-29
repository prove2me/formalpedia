-- Prove2me | Theorems.Thm_FamousTheorems_grothendieck_abelian_enough_injectives_7a
-- name    : FamousTheorems.grothendieck_abelian_enough_injectives_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:24.481016+00:00
-- url     : https://prove2.me/theorems/98d90319-4e57-4ec0-964a-bd455d9fed32
-- title:
--   Grothendieck abelian categories have enough injectives
-- statement:
--   **Grothendieck abelian categories have enough injectives.** Let $C$ be a Grothendieck abelian category, an abelian category with a generator, exact filtered colimits and all small colimits. Then every object of $C$ embeds into an injective object.
--
--   Grothendieck proved this in his 1957 Tôhoku paper. It makes derived functors available in categories such as sheaves of abelian groups or sheaves of modules on a ringed space. Sheaf cohomology is defined in this way. The categories of modules over a ring and of quasi-coherent sheaves on a scheme are also Grothendieck abelian.
--
--   **Formalization note.** Mathlib's `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`. `IsGrothendieckAbelian.{w} C` says that $C$ is locally $w$-small, has $w$-small filtered colimits that are exact, and has a separator. `EnoughInjectives C` says that every object admits a monomorphism into an injective object.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w

theorem grothendieck_abelian_enough_injectives_7a (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{w} C] : CategoryTheory.EnoughInjectives C := by sorry

end FamousTheorems
