-- Prove2me | Theorems.Thm_FamousTheorems_yoneda_embedding_full_6b
-- name    : FamousTheorems.yoneda_embedding_full_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:45.186976+00:00
-- url     : https://prove2.me/theorems/f4dce3af-7cd3-4395-a0a2-59f09e24c4e7
-- title:
--   The Yoneda embedding is full
-- statement:
--   **The Yoneda embedding is full.** For every category $\mathcal C$, the Yoneda functor $y:\mathcal C\to[\mathcal C^{\mathrm{op}},\mathbf{Set}]$, $X\mapsto\operatorname{Hom}(-,X)$, is full: every natural transformation $\operatorname{Hom}(-,X)\to\operatorname{Hom}(-,Y)$ is of the form $\operatorname{Hom}(-,f)$ for some morphism $f:X\to Y$.
--
--   This is the case $F=\operatorname{Hom}(-,Y)$ of the Yoneda lemma. Since $y$ is also faithful, $\mathcal C$ embeds as a full subcategory of its presheaf category. This embedding makes it possible to check statements about objects through their representable presheaves, and it is used to embed categories into complete and cocomplete ones.
--
--   **Formalization note.** Mathlib's instance `CategoryTheory.Yoneda.yoneda_full`. `yoneda : C ⥤ Cᵒᵖ ⥤ Type v` takes values in presheaves of types in the morphism universe of $\mathcal C$. `Functor.Full` says that every morphism between images is the image of a morphism. The statement is proved by `inferInstance`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Yoneda.yoneda_full`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open CategoryTheory

theorem yoneda_embedding_full_6b (C : Type*) [Category C] : (yoneda : C ⥤ Cᵒᵖ ⥤ Type _).Full := by sorry

end FamousTheorems
