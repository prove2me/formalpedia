-- Prove2me | Theorems.Thm_CPAMMFlaws_Properties_lemma_2
-- name    : CPAMMFlaws.Properties.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:31.601069+00:00
-- url     : https://prove2.me/theorems/46af88cb-2fc3-4a68-aee2-1b63606765e8
-- title:
--   Lemma 2, p. 15 — the constant product invariant (X − x)(Y + y) = XY holds exactly when y = p^cmm(x, X, Y) = xY/(X − x)
-- statement:
--   Let a constant product pool hold $X>0$ units of token $A$ and $Y>0$ units of token $B$, and let $x<X$ be the quantity of $A$ traded ($x>0$ a buy, $x<0$ a sale). Then:
--
--   1. for every real $y$, the pool stays on its constant product curve,
--   $$
--   (X-x)(Y+y)=XY \iff y=p^{\mathrm{cmm}}(x,X,Y)=\frac{xY}{X-x};
--   $$
--   2. after the trade the pool holds
--   $$
--   Y+p^{\mathrm{cmm}}(x,X,Y)=\frac{XY}{X-x}
--   $$
--   units of $B$.
--
--   This is the bridge between the pricing rule $(X-x)(Y+y)=c=XY$ of §II.C and the closed form (3) used in every later computation, together with the paper's description of the pool after the trade.
--
--   **Formalization Note** The page allows demand $x\in(-\infty,X]$; at $x=X$ no $y$ satisfies the invariant, so the lemma is stated for $x<X$. $X>0$, $Y>0$ are the deposits of §II.C. Part 2 is the sentence after the lemma: "After the trade, the contract contains $X-x$ units of token $A$, and $XY/(X-x)$ units of $B$."
-- source:
--   Park, The Conceptual Flaws of Constant Product Automated Market Making, working paper dated June 8, 2021, p. 15, Lemma 2, (3), and the sentence after it; invariant from §II.C, p. 14

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting

namespace CPAMMFlaws.Properties

theorem lemma_2 (X Y x : ℝ) (hX : 0 < X) (hY : 0 < Y) (hxX : x < X) :
    (∀ y : ℝ, (X - x) * (Y + y) = X * Y ↔ y = pcmm x X Y) ∧
      Y + pcmm x X Y = X * Y / (X - x) := by sorry

end CPAMMFlaws.Properties
