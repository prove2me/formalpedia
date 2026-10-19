-- Prove2me | Theorems.Thm_ContinuumHypothesis_gch_two_pow_strictMono
-- name    : ContinuumHypothesis.gch_two_pow_strictMono
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T22:33:59.156293+00:00
-- url     : https://prove2.me/theorems/ca5ac016-41d1-4012-9234-582cf2c48528
-- title:
--   GCH $\Rightarrow$ ($A<B\Rightarrow 2^A<2^B$) for infinite $A$
-- statement:
--   Assume the generalized continuum hypothesis. Then for all cardinals $A,B$ with $A$ infinite,
--   $$A<B\ \Longrightarrow\ 2^A<2^B .$$
--   (Without GCH only $2^A\le 2^B$ follows; the strict form always holds for finite cardinals.)
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; section 'Generalized continuum hypothesis', paragraph 5 ('GCH implies that this strict, stronger inequality holds for infinite cardinals as well as finite cardinals').

import Definitions.Def_CH_CardinalArithmetic
open Cardinal
universe u

namespace ContinuumHypothesis

theorem gch_two_pow_strictMono (h : GCH.{u}) (A B : Cardinal.{u}) (hA : ℵ₀ ≤ A) (hAB : A < B) :
    (2 : Cardinal.{u}) ^ A < 2 ^ B := by sorry

end ContinuumHypothesis
