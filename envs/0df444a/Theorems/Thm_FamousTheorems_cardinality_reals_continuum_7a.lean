-- Prove2me | Theorems.Thm_FamousTheorems_cardinality_reals_continuum_7a
-- name    : FamousTheorems.cardinality_reals_continuum_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:48.585659+00:00
-- url     : https://prove2.me/theorems/a1b7b536-c28f-49b6-b8f9-4f027282bc4d
-- title:
--   The cardinality of ℝ is the continuum
-- statement:
--   **The cardinality of $\mathbb R$ is the continuum.** $|\mathbb R|=\mathfrak c=2^{\aleph_0}$.
--
--   Cantor proved in 1874 that $\mathbb R$ is uncountable and later identified its cardinality with that of the power set of $\mathbb N$, for example through binary expansions or Dedekind cuts. The continuum hypothesis asks whether there is a cardinal strictly between $\aleph_0$ and $|\mathbb R|$. Gödel and Cohen showed that it is independent of ZFC.
--
--   **Formalization note.** Mathlib's `Cardinal.mk_real`. `Cardinal.continuum` is defined as $2^{\aleph_0}$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Cardinal.mk_real`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cardinality_reals_continuum_7a : Cardinal.mk ℝ = Cardinal.continuum := by sorry

end FamousTheorems
