-- Prove2me | Theorems.Thm_Algebra_WeaklyEtale_exists_indEtale
-- name    : Algebra.WeaklyEtale.exists_indEtale
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:27:28.784279+00:00
-- url     : https://prove2.me/theorems/8a5984e3-ff90-5603-a013-07fe1049954a
-- title:
--   Theorem 2.3.4 — a weakly étale ring map becomes ind-étale after a faithfully flat ind-étale extension
-- statement:
--   Let $R$ be a commutative ring and $S$ a commutative $R$-algebra. Recall that $S$ is **weakly étale** over $R$ if $S$ is flat over $R$ and the multiplication map $S \otimes_R S \to S$ is flat, and that an algebra is **ind-étale** if it is a filtered colimit of étale algebras.
--
--   Suppose $S$ is weakly étale over $R$. Then there exists a commutative $S$-algebra $T$ such that
--
--   1. $T$ is ind-étale over $S$;
--   2. $T$ is faithfully flat over $S$;
--   3. $T$ is ind-étale over $R$.
--
--   In the notation of the paper: for $f : A \to B$ weakly étale there is a faithfully flat ind-étale $g : B \to C$ with $g \circ f$ ind-étale.
--
--   This is the algebraic input that lets one replace weakly étale maps by ind-étale ones when working locally on the pro-étale site; it is what shows that pro-étale affines generate the site.
--
--   **Formalization Note** $R$, $S$ and $T$ live in one universe. The $R$-algebra structure on $T$ is part of the existential data, together with the compatibility `IsScalarTower R S T`. Ind-étale is `Algebra.IndEtale`: existence of a colimit presentation of the algebra, indexed by a small filtered category, all of whose terms are étale.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Theorem 2.3.4 (p. 12 of the arXiv v2 PDF); same statement as Theorem 1.3(3). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WeaklyEtaleIndEtale.lean, lines 187-329 (`Algebra.WeaklyEtale.exists_indEtale`).

import Mathlib
import Definitions.Def_ProEtale_Algebra_IndEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u
open PrimeSpectrum TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem Algebra.WeaklyEtale.exists_indEtale [Algebra.WeaklyEtale R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra S T) (_ : IsScalarTower R S T),
      Algebra.IndEtale S T ∧ Module.FaithfullyFlat S T ∧ Algebra.IndEtale R T := by sorry
