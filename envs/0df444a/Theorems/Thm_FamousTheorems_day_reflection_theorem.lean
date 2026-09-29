-- Prove2me | Theorems.Thm_FamousTheorems_day_reflection_theorem
-- name    : FamousTheorems.day_reflection_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:55.756766+00:00
-- url     : https://prove2.me/theorems/53f382e6-facf-4110-a36c-db982b1e068d
-- title:
--   Day's reflection theorem
-- statement:
--   **Day's reflection theorem.** Let $D$ be a symmetric monoidal closed category, and let $R:C\to D$ be a fully faithful right adjoint with left adjoint $L$ and unit $\eta$. The following are equivalent:
--   1. $\eta_{[d,Rc]}$ is an isomorphism for all $c\in C$ and $d\in D$;
--   2. the precomposition map $[RLd,Rc]\to[d,Rc]$ induced by $\eta_d$ is an isomorphism for all $c,d$;
--   3. $L(\eta_d\otimes d')$ is an isomorphism for all $d,d'$;
--   4. $L(\eta_d\otimes\eta_{d'})$ is an isomorphism for all $d,d'$.
--
--   Day proved this in 1972. It characterises the reflective subcategories of a closed symmetric monoidal category that are exponential ideals, and for which the reflector is strong monoidal. The monoidal structure then descends to the subcategory. Standard examples include sheafification and localisations of module categories.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Monoidal.Reflective.isIso_tfae`. `ihom d` is the internal-hom functor $[d,-]$, `MonoidalClosed.pre f` is precomposition with $f$ on internal homs, `▷` is right whiskering and `⊗ₘ` is the tensor product of morphisms. Full faithfulness of $R$ is given by the instances `R.Full` and `R.Faithful`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Monoidal.Reflective.isIso_tfae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open CategoryTheory MonoidalCategory

theorem day_reflection_theorem {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalClosed D] {R : Functor C D} [R.Faithful] [R.Full] {L : Functor D C} (adj : L ⊣ R) :
    List.TFAE [∀ (c : C) (d : D), IsIso (adj.unit.app ((ihom d).obj (R.obj c))),
      ∀ (c : C) (d : D), IsIso ((MonoidalClosed.pre (adj.unit.app d)).app (R.obj c)),
      ∀ d d' : D, IsIso (L.map (adj.unit.app d ▷ d')),
      ∀ d d' : D, IsIso (L.map (adj.unit.app d ⊗ₘ adj.unit.app d'))] := by sorry

end FamousTheorems
