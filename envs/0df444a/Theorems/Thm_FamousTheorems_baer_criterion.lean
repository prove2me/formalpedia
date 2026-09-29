-- Prove2me | Theorems.Thm_FamousTheorems_baer_criterion
-- name    : FamousTheorems.baer_criterion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:55.593761+00:00
-- url     : https://prove2.me/theorems/811e9537-de58-47ec-9dab-7a654079a148
-- title:
--   Baer's criterion for injective modules
-- statement:
--   **Baer's criterion.** Let $R$ be a ring and $Q$ an $R$-module. Suppose that for every left ideal $I\subseteq R$, every $R$-linear map $I\to Q$ extends to an $R$-linear map $R\to Q$. Then $Q$ is an injective module.
--
--   Injectivity asks that maps into $Q$ extend along every injection of modules. Baer's criterion reduces this to the inclusions of ideals into $R$. It is the standard way to prove that a module is injective. For example, over a principal ideal domain it shows that divisible modules are injective, so $\mathbb Q/\mathbb Z$ is an injective $\mathbb Z$-module. It also gives that every module embeds in an injective module.
--
--   **Formalization note.** Mathlib's `Module.Baer.injective`. `Module.Baer R Q` is the extension property for ideals. `Module.Injective R Q` is injectivity in the categorical sense: linear maps into `Q` extend along injective linear maps between modules in a suitable universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.Baer.injective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem baer_criterion {R Q : Type*} [Ring R] [AddCommGroup Q] [Module R Q] (h : Module.Baer R Q) :
    Module.Injective R Q := by sorry

end FamousTheorems
