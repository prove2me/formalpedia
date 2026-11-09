-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_proposition_2_3
-- name    : DetStreamClique.MaxClique.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:24.526998+00:00
-- url     : https://prove2.me/theorems/6fc04726-5255-41c3-a70d-c24af9adb809
-- title:
--   Proposition 2.3 — product-law superadditivity
-- statement:
--   Let $X=(X_i)_{i\in I}$ be a tuple of finite-valued random variables with finite index set $I$, and let $Y,Z$ be finite-valued on the same finite probability space. Suppose $P(Y=y,Z=z)>0$ and the conditional law of $X$ given $Z=z$ is the product of its marginal laws. Then
--   $$\sum_{i\in I}J(X_i\mid Y=y,Z=z)\le J(X\mid Y=y,Z=z).$$
--   No product structure is assumed after conditioning on $Y=y$. The result controls the information delivered to the individual gadgets.
--
--   Differences from the source:
--   - encoding: conditional distributions at realized messages and background values → positive conditioning events or nonempty message fibers; reason: realized finite-law values have positive probability; undefined null conditionings are excluded
--   - encoding: a tuple (X₁,…,Xℓ) with a product conditional law → a finite dependent product indexed by I and equality of joint and product marginal atom masses; reason: every tuple in the source is represented by I=Fin ℓ, including an empty tuple
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Proposition 2.3, p. 9

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Information

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Proposition 2.3, p. 9; independence only before conditioning on the message. -/
theorem proposition_2_3 {Ω I Y Z : Type} {X : I → Type}
    [Fintype Ω] [Fintype I] [∀ i, Fintype (X i)] [Fintype Y] [Fintype Z]
    (P : FiniteLaw Ω) (x : Ω → ((i : I) → X i)) (y : Ω → Y) (z : Ω → Z)
    (y₀ : Y) (z₀ : Z)
    (hpos : 0 < eventProb P (fun w => y w = y₀ ∧ z w = z₀))
    (hprod : ConditionalProduct P x z z₀) :
    (∑ i, messageInformation P (fun w => x w i) y y₀ z z₀) ≤
      messageInformation P x y y₀ z z₀ := by sorry

end DetStreamClique.MaxClique
