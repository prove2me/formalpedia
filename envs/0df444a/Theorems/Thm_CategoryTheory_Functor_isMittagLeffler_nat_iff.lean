-- Prove2me | Theorems.Thm_CategoryTheory_Functor_isMittagLeffler_nat_iff
-- name    : CategoryTheory.Functor.isMittagLeffler_nat_iff
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:42.488887+00:00
-- url     : https://prove2.me/theorems/64a0fbaa-aba9-43fd-9296-6e8148f83448
-- title:
--   The Mittag-Leffler condition for an $\mathbb{N}$-indexed inverse system of sets, in explicit form
-- statement:
--   Let $F : \mathbb{N}^{\mathrm{op}} \to \mathbf{Set}$ be an inverse system of sets, and for $n \le m$ write $F_{m,n} : F(m) \to F(n)$ for its transition map. Then $F$ satisfies the Mittag-Leffler condition if and only if
--   $$\forall n \;\exists m \ge n \;\forall k \ge n : \quad \operatorname{im}(F_{m,n}) \subseteq \operatorname{im}(F_{k,n}).$$
--
--   The general Mittag-Leffler condition for a cofiltered system asks, for every index $j$, for a morphism $i \to j$ whose image is contained in the image of every morphism $k \to j$; this lemma specializes it to the index category $\mathbb{N}^{\mathrm{op}}$, giving the familiar form used in arguments about $\varprojlim^1$.
--
--   **Formalization Note** The functor is `F : ℕᵒᵖ ⥤ Type v` and Mittag-Leffler is Mathlib's `Functor.IsMittagLeffler`. Transition maps are written `F.map (homOfLE h).op`, and images as `Set.range`. Note that $k$ ranges over all $k \ge n$, not only $k \ge m$. The Lean name is `CategoryTheory.Functor.isMittagLeffler_nat_iff`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/CofilteredSystem.lean, lines 57-78 (`CategoryTheory.Functor.isMittagLeffler_nat_iff`).

import Mathlib.CategoryTheory.CofilteredSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w v u

open Set

namespace CategoryTheory
namespace Functor

variable (F : ℕᵒᵖ ⥤ Type v)

open Opposite in

theorem isMittagLeffler_nat_iff :
    F.IsMittagLeffler ↔ ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      range (F.map (homOfLE hm).op) ⊆ range (F.map (homOfLE hk).op) := by sorry

end Functor
end CategoryTheory
