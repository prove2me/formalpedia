-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_orderedAffineCover_orderEmbedding_of_sup_eq_top
-- name    : AlgebraicGeometry.Scheme.exists_orderedAffineCover_orderEmbedding_of_sup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/ea4a326f-7937-522d-939d-05df83140772
-- title:
--   Concatenating ordered affine covers of two opens covering X
-- statement:
--   Let $X$ be a scheme and let $U, V$ be open subschemes of $X$ (elements of `X.Opens`) with $U \sqcup V = \top$, i.e. $U \cup V = X$. Let $\mathfrak V$ be an ordered affine cover of the scheme $V$ and $\mathfrak U$ one of the scheme $U$; here an ordered affine cover of a scheme $W$ consists of a finite linearly ordered index type together with a family of opens of $W$ indexed by it, each of which is an affine open, whose supremum is $\top$. The assertion is that there exists an ordered affine cover $\mathfrak X'$ of $X$ together with order embeddings $e_V \colon \mathfrak V.\iota \hookrightarrow \mathfrak X'.\iota$ and $e_U \colon \mathfrak U.\iota \hookrightarrow \mathfrak X'.\iota$ of the two index types into that of $\mathfrak X'$ such that: for every $b$, the chart of $\mathfrak X'$ at $e_V(b)$ is the image of the chart $\mathfrak V.U\,b$ under the open immersion $V \to X$; for every $a$, the chart at $e_U(a)$ is the image of $\mathfrak U.U\,a$ under $U \to X$; $e_V(b) < e_U(a)$ for all $b$ and $a$, so all charts coming from $V$ precede all charts coming from $U$; and every index of $\mathfrak X'$ lies in the range of $e_V$ or in the range of $e_U$.
--
--   This is the concatenation (ordered disjoint union) of affine covers of the two members of a two-open cover of $X$, with the charts of $V$ placed before those of $U$; the conclusion is phrased as the existence of index-preserving order embeddings rather than via a new gluing construction. It is used in the Mayer–Vietoris style comparison of Čech complexes, namely by [`AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_orderedAffineCover_orderEmbedding_of_sup_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_orderedAffineCover_orderEmbedding_of_sup_eq_top
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover) :
    ∃ (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι),
      (∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) ∧ (∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a) ∧
      (∀ b a, eV b < eU a) ∧ ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU := by sorry
