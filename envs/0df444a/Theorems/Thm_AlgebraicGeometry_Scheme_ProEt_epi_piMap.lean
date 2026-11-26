-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_epi_piMap
-- name    : AlgebraicGeometry.Scheme.ProEt.epi_piMap
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:30:57.166749+00:00
-- url     : https://prove2.me/theorems/2f3034f6-daf9-5dd0-8711-b494ffcd8fa5
-- title:
--   Products of epimorphisms of abelian pro-étale sheaves are epimorphisms
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $\iota$ be a set that is small relative to the universe of abelian sheaves, and let $\varphi_i : A_i \to B_i$, $i \in \iota$, be a family of morphisms of sheaves of abelian groups on $X_{\text{proét}}$. If every $\varphi_i$ is an epimorphism, then
--
--   $$
--   \prod_{i \in \iota} \varphi_i \;:\; \prod_{i \in \iota} A_i \longrightarrow \prod_{i \in \iota} B_i
--   $$
--
--   is an epimorphism of sheaves.
--
--   This exactness of products is not available in general on the étale site. It is used to control inverse limits of sheaves on the pro-étale site.
--
--   **Formalization Note** Sheaves take values in `Ab.{u + 1}` for $X$ a `Scheme.{u}`, and $\iota$ is any type with `Small.{u + 1} ι`. The paper's Proposition 3.1.9 is stated for countable products in an arbitrary replete topos; this statement is specific to $\operatorname{Shv}(X_{\text{proét}})$ and allows arbitrary small products.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Compare Proposition 3.1.9, p. 17 of the arXiv v2 PDF (countable products are exact in a replete topos); the statement here is not that proposition: it concerns the pro-étale topos only and arbitrary small index sets. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/RepleteExact.lean, lines 265-309 (`AlgebraicGeometry.Scheme.ProEt.epi_piMap`).

import Mathlib
import Definitions.Def_ProEtale_Topology_Comparison_RepleteExact

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w w' u
open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
variable {S : Scheme.{u}}
variable (F G : Sheaf (ProEt.topology S) Ab.{u + 1})

theorem AlgebraicGeometry.Scheme.ProEt.epi_piMap {ι : Type w} [Small.{u + 1} ι]
    (A B : ι → Sheaf (ProEt.topology S) Ab.{u + 1}) (φ : ∀ i, A i ⟶ B i)
    [∀ i, Epi (φ i)] : Epi (Limits.Pi.map φ) := by sorry
