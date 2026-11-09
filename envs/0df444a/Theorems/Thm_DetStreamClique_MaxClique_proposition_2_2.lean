-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_proposition_2_2
-- name    : DetStreamClique.MaxClique.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:02:41.935235+00:00
-- url     : https://prove2.me/theorems/f7d1840c-4f6a-4b39-8e84-59ac0164d255
-- title:
--   Proposition 2.2 — averaging message-wise information
-- statement:
--   Let $X,Y,Z$ be finite-valued random variables on a common finite probability space, and let $P(Z=z)>0$. Then
--   $$I(X;Y\mid Z=z)=\sum_{y:P(Y=y,Z=z)>0}P(Y=y\mid Z=z)\,J(X\mid Y=y,Z=z).$$
--   The conditional mutual information on the left is defined through joint entropies. The identity relates the message-wise entropy drop to its conditional average.
--
--   Differences from the source:
--   - encoding: conditional distributions at realized messages and background values → positive conditioning events or nonempty message fibers; reason: realized finite-law values have positive probability; undefined null conditionings are excluded
--   - encoding: finite Shannon entropies in bits → published finite-law entropy divided by log 2, with finite marginal sums; reason: this is the same entropy and conditional law on every positive event
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Proposition 2.2, p. 9

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Information

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Proposition 2.2, p. 9; the sum ranges over positive joint atoms. -/
theorem proposition_2_2 {Ω X Y Z : Type}
    [Fintype Ω] [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteLaw Ω) (x : Ω → X) (y : Ω → Y) (z : Ω → Z) (z₀ : Z)
    (hz : 0 < eventProb P (fun w => z w = z₀)) :
    mutualAt P x y (fun w => z w = z₀) =
      ∑ y₀, if 0 < eventProb P (fun w => y w = y₀ ∧ z w = z₀) then
        (eventProb P (fun w => y w = y₀ ∧ z w = z₀) /
          eventProb P (fun w => z w = z₀)) * messageInformation P x y y₀ z z₀
        else 0 := by sorry

end DetStreamClique.MaxClique
