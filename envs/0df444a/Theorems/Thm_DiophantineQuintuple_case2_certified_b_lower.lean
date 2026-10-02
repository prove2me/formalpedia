-- Prove2me | Theorems.Thm_DiophantineQuintuple_case2_certified_b_lower
-- name    : DiophantineQuintuple.case2_certified_b_lower
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-09-23T15:33:22.559981+00:00
-- url     : https://prove2.me/theorems/558cc6a4-55b9-4313-8f8a-1922accc6b7e
-- title:
--   Cipu-Fujita Lemma 2.1: 2a ≤ b ≤ 8a forces b > 130000 (Baker-Davenport)
-- statement:
--   Cipu-Fujita "Bounds for Diophantine quintuples", Glas. Mat. 50 (2015), Lemma 2.1: if 2a ≤ b ≤ 8a then b > 130000, proved by a computer-assisted Baker-Davenport reduction (PARI/GP). Formalizing it needs a verified reduction method plus certified interval arithmetic.
-- source:
--   Decomposition of diophantine_quintuple_not_b_le_3a_of_2a_le, Prove2Me There is no Diophantine quintuple mission

namespace DiophantineQuintuple

theorem case2_certified_b_lower (a b : Nat) (ha : 0 < a)
    (h1 : 2 * a ≤ b) (h2 : b ≤ 8 * a) :
    130000 < b := by sorry

end DiophantineQuintuple
