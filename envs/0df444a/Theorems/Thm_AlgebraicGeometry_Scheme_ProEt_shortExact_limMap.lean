-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_shortExact_limMap
-- name    : AlgebraicGeometry.Scheme.ProEt.shortExact_limMap
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:31:33.821271+00:00
-- url     : https://prove2.me/theorems/04c90b36-38a4-5bc8-8738-d8b65d4d02fa
-- title:
--   Inverse limits of short exact sequences of towers of abelian pro-étale sheaves
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let
--
--   $$
--   0 \to F' \to F \to F'' \to 0
--   $$
--
--   be a sequence of towers ($\mathbb N^{\mathrm{op}}$-indexed inverse systems) of sheaves of abelian groups on $X_{\text{proét}}$ which is short exact in each level $k \in \mathbb N$. Assume that every transition map $F'_{n+1} \to F'_n$ of the first tower is an epimorphism. Then the sequence of inverse limits
--
--   $$
--   0 \to \varprojlim_n F'_n \to \varprojlim_n F_n \to \varprojlim_n F''_n \to 0
--   $$
--
--   is short exact.
--
--   This is the Mittag-Leffler property of the pro-étale topos: the first derived inverse limit of a tower with epimorphic transition maps vanishes. It is what allows $\ell$-adic sheaves to be treated as honest inverse limits.
--
--   **Formalization Note** The sequence is a `ShortComplex` in the functor category `ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}`; the hypothesis is that its image under each evaluation functor is short exact, and the conclusion that its image under `lim` is short exact. Proposition 3.1.10 of the paper asserts $\varprojlim F_n \simeq R\varprojlim F_n$ in any replete topos; the exact-sequence form stated here is equivalent in content but is not the paper's wording.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Compare Proposition 3.1.10, p. 17 of the arXiv v2 PDF (lim = R lim for towers with surjective transition maps in a replete topos); the statement here is a reformulation, for the pro-étale topos only. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/RepleteExact.lean, lines 313-448 (`AlgebraicGeometry.Scheme.ProEt.shortExact_limMap`).

import Mathlib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Topology_Comparison_RepleteExact
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification

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
variable {T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1})}

theorem AlgebraicGeometry.Scheme.ProEt.shortExact_limMap
    (hT : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
      (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)).ShortExact)
    (h1 : ∀ n, Epi (SequentialSystem.transition T.X₁ n)) :
    (T.map lim).ShortExact := by sorry
