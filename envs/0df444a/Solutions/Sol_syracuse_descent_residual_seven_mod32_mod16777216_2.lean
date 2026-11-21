-- Prove2me | solution 2 for syracuse_descent_residual_seven_mod32_mod16777216
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-20T10:47:45.667189+00:00
-- url     : https://prove2.me/submissions/a5a4f2c2-4a1e-4e7d-a169-4753f4ecc5a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_descent_residual_seven_mod32_mod16777216_refined
import Theorems.Thm_syracuse_descends_below_2310000

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem certifiedStep (x y k : ℕ)
    (he : 3 * x + 1 = 2 ^ k * y) (ho : ¬ 2 ∣ y) :
    syracuseStep x = y := by
  unfold syracuseStep
  rw [he, Nat.ordCompl_pow_mul_of_not_dvd k Nat.prime_two ho]

private theorem descent_743 (q : ℕ) :
    syracuseStep^[15] (743 + 33554432 * q) < 743 + 33554432 * q := by
  have h1 : syracuseStep (743 + 33554432 * q) = 1115 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (1115 + 50331648 * q) = 1673 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (1673 + 75497472 * q) = 1255 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (1255 + 56623104 * q) = 1883 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (1883 + 84934656 * q) = 2825 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (2825 + 127401984 * q) = 2119 + 95551488 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h7 : syracuseStep (2119 + 95551488 * q) = 3179 + 143327232 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (3179 + 143327232 * q) = 4769 + 214990848 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (4769 + 214990848 * q) = 3577 + 161243136 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h10 : syracuseStep (3577 + 161243136 * q) = 2683 + 120932352 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h11 : syracuseStep (2683 + 120932352 * q) = 4025 + 181398528 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (4025 + 181398528 * q) = 3019 + 136048896 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h13 : syracuseStep (3019 + 136048896 * q) = 4529 + 204073344 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (4529 + 204073344 * q) = 3397 + 153055008 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (3397 + 153055008 * q) = 637 + 28697814 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_4839 (q : ℕ) :
    syracuseStep^[15] (4839 + 33554432 * q) < 4839 + 33554432 * q := by
  have h1 : syracuseStep (4839 + 33554432 * q) = 7259 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (7259 + 50331648 * q) = 10889 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (10889 + 75497472 * q) = 8167 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (8167 + 56623104 * q) = 12251 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (12251 + 84934656 * q) = 18377 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (18377 + 127401984 * q) = 13783 + 95551488 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h7 : syracuseStep (13783 + 95551488 * q) = 20675 + 143327232 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (20675 + 143327232 * q) = 31013 + 214990848 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (31013 + 214990848 * q) = 5815 + 40310784 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  have h10 : syracuseStep (5815 + 40310784 * q) = 8723 + 60466176 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (8723 + 60466176 * q) = 13085 + 90699264 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (13085 + 90699264 * q) = 4907 + 34012224 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h13 : syracuseStep (4907 + 34012224 * q) = 7361 + 51018336 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (7361 + 51018336 * q) = 5521 + 38263752 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (5521 + 38263752 * q) = 4141 + 28697814 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_5735 (q : ℕ) :
    syracuseStep^[15] (5735 + 33554432 * q) < 5735 + 33554432 * q := by
  have h1 : syracuseStep (5735 + 33554432 * q) = 8603 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (8603 + 50331648 * q) = 12905 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (12905 + 75497472 * q) = 9679 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (9679 + 56623104 * q) = 14519 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (14519 + 84934656 * q) = 21779 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (21779 + 127401984 * q) = 32669 + 191102976 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (32669 + 191102976 * q) = 12251 + 71663616 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h8 : syracuseStep (12251 + 71663616 * q) = 18377 + 107495424 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (18377 + 107495424 * q) = 13783 + 80621568 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h10 : syracuseStep (13783 + 80621568 * q) = 20675 + 120932352 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (20675 + 120932352 * q) = 31013 + 181398528 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (31013 + 181398528 * q) = 5815 + 34012224 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  have h13 : syracuseStep (5815 + 34012224 * q) = 8723 + 51018336 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (8723 + 51018336 * q) = 13085 + 76527504 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h15 : syracuseStep (13085 + 76527504 * q) = 4907 + 28697814 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_7335 (q : ℕ) :
    syracuseStep^[15] (7335 + 33554432 * q) < 7335 + 33554432 * q := by
  have h1 : syracuseStep (7335 + 33554432 * q) = 11003 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (11003 + 50331648 * q) = 16505 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (16505 + 75497472 * q) = 12379 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (12379 + 56623104 * q) = 18569 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (18569 + 84934656 * q) = 13927 + 63700992 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h6 : syracuseStep (13927 + 63700992 * q) = 20891 + 95551488 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (20891 + 95551488 * q) = 31337 + 143327232 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (31337 + 143327232 * q) = 23503 + 107495424 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h9 : syracuseStep (23503 + 107495424 * q) = 35255 + 161243136 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (35255 + 161243136 * q) = 52883 + 241864704 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (52883 + 241864704 * q) = 79325 + 362797056 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (79325 + 362797056 * q) = 29747 + 136048896 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h13 : syracuseStep (29747 + 136048896 * q) = 44621 + 204073344 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (44621 + 204073344 * q) = 16733 + 76527504 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h15 : syracuseStep (16733 + 76527504 * q) = 6275 + 28697814 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_9287 (q : ℕ) :
    syracuseStep^[15] (9287 + 33554432 * q) < 9287 + 33554432 * q := by
  have h1 : syracuseStep (9287 + 33554432 * q) = 13931 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (13931 + 50331648 * q) = 20897 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (20897 + 75497472 * q) = 15673 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (15673 + 56623104 * q) = 11755 + 42467328 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h5 : syracuseStep (11755 + 42467328 * q) = 17633 + 63700992 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (17633 + 63700992 * q) = 13225 + 47775744 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h7 : syracuseStep (13225 + 47775744 * q) = 9919 + 35831808 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h8 : syracuseStep (9919 + 35831808 * q) = 14879 + 53747712 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (14879 + 53747712 * q) = 22319 + 80621568 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (22319 + 80621568 * q) = 33479 + 120932352 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (33479 + 120932352 * q) = 50219 + 181398528 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (50219 + 181398528 * q) = 75329 + 272097792 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h13 : syracuseStep (75329 + 272097792 * q) = 56497 + 204073344 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h14 : syracuseStep (56497 + 204073344 * q) = 42373 + 153055008 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (42373 + 153055008 * q) = 7945 + 28697814 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_9575 (q : ℕ) :
    syracuseStep^[15] (9575 + 33554432 * q) < 9575 + 33554432 * q := by
  have h1 : syracuseStep (9575 + 33554432 * q) = 14363 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (14363 + 50331648 * q) = 21545 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (21545 + 75497472 * q) = 16159 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (16159 + 56623104 * q) = 24239 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (24239 + 84934656 * q) = 36359 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (36359 + 127401984 * q) = 54539 + 191102976 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (54539 + 191102976 * q) = 81809 + 286654464 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (81809 + 286654464 * q) = 61357 + 214990848 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h9 : syracuseStep (61357 + 214990848 * q) = 23009 + 80621568 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h10 : syracuseStep (23009 + 80621568 * q) = 17257 + 60466176 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h11 : syracuseStep (17257 + 60466176 * q) = 12943 + 45349632 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h12 : syracuseStep (12943 + 45349632 * q) = 19415 + 68024448 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h13 : syracuseStep (19415 + 68024448 * q) = 29123 + 102036672 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (29123 + 102036672 * q) = 43685 + 153055008 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h15 : syracuseStep (43685 + 153055008 * q) = 8191 + 28697814 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_11495 (q : ℕ) :
    syracuseStep^[15] (11495 + 33554432 * q) < 11495 + 33554432 * q := by
  have h1 : syracuseStep (11495 + 33554432 * q) = 17243 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (17243 + 50331648 * q) = 25865 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (25865 + 75497472 * q) = 19399 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (19399 + 56623104 * q) = 29099 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (29099 + 84934656 * q) = 43649 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (43649 + 127401984 * q) = 32737 + 95551488 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h7 : syracuseStep (32737 + 95551488 * q) = 24553 + 71663616 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h8 : syracuseStep (24553 + 71663616 * q) = 18415 + 53747712 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h9 : syracuseStep (18415 + 53747712 * q) = 27623 + 80621568 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (27623 + 80621568 * q) = 41435 + 120932352 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (41435 + 120932352 * q) = 62153 + 181398528 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (62153 + 181398528 * q) = 46615 + 136048896 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h13 : syracuseStep (46615 + 136048896 * q) = 69923 + 204073344 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (69923 + 204073344 * q) = 104885 + 306110016 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h15 : syracuseStep (104885 + 306110016 * q) = 9833 + 28697814 * q := by
    apply certifiedStep _ _ 5
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_14247 (q : ℕ) :
    syracuseStep^[15] (14247 + 33554432 * q) < 14247 + 33554432 * q := by
  have h1 : syracuseStep (14247 + 33554432 * q) = 21371 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (21371 + 50331648 * q) = 32057 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (32057 + 75497472 * q) = 24043 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (24043 + 56623104 * q) = 36065 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (36065 + 84934656 * q) = 27049 + 63700992 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h6 : syracuseStep (27049 + 63700992 * q) = 20287 + 47775744 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h7 : syracuseStep (20287 + 47775744 * q) = 30431 + 71663616 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (30431 + 71663616 * q) = 45647 + 107495424 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (45647 + 107495424 * q) = 68471 + 161243136 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (68471 + 161243136 * q) = 102707 + 241864704 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (102707 + 241864704 * q) = 154061 + 362797056 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (154061 + 362797056 * q) = 57773 + 136048896 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h13 : syracuseStep (57773 + 136048896 * q) = 21665 + 51018336 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h14 : syracuseStep (21665 + 51018336 * q) = 16249 + 38263752 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (16249 + 38263752 * q) = 12187 + 28697814 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_15975 (q : ℕ) :
    syracuseStep^[14] (15975 + 33554432 * q) < 15975 + 33554432 * q := by
  have h1 : syracuseStep (15975 + 33554432 * q) = 23963 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (23963 + 50331648 * q) = 35945 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (35945 + 75497472 * q) = 26959 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (26959 + 56623104 * q) = 40439 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (40439 + 84934656 * q) = 60659 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (60659 + 127401984 * q) = 90989 + 191102976 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (90989 + 191102976 * q) = 34121 + 71663616 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h8 : syracuseStep (34121 + 71663616 * q) = 25591 + 53747712 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h9 : syracuseStep (25591 + 53747712 * q) = 38387 + 80621568 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (38387 + 80621568 * q) = 57581 + 120932352 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (57581 + 120932352 * q) = 21593 + 45349632 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h12 : syracuseStep (21593 + 45349632 * q) = 16195 + 34012224 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h13 : syracuseStep (16195 + 34012224 * q) = 24293 + 51018336 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (24293 + 51018336 * q) = 4555 + 9565938 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  omega

private theorem descent_16231 (q : ℕ) :
    syracuseStep^[15] (16231 + 33554432 * q) < 16231 + 33554432 * q := by
  have h1 : syracuseStep (16231 + 33554432 * q) = 24347 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (24347 + 50331648 * q) = 36521 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (36521 + 75497472 * q) = 27391 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (27391 + 56623104 * q) = 41087 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (41087 + 84934656 * q) = 61631 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (61631 + 127401984 * q) = 92447 + 191102976 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (92447 + 191102976 * q) = 138671 + 286654464 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (138671 + 286654464 * q) = 208007 + 429981696 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (208007 + 429981696 * q) = 312011 + 644972544 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (312011 + 644972544 * q) = 468017 + 967458816 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (468017 + 967458816 * q) = 351013 + 725594112 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h12 : syracuseStep (351013 + 725594112 * q) = 65815 + 136048896 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  have h13 : syracuseStep (65815 + 136048896 * q) = 98723 + 204073344 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (98723 + 204073344 * q) = 148085 + 306110016 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h15 : syracuseStep (148085 + 306110016 * q) = 13883 + 28697814 * q := by
    apply certifiedStep _ _ 5
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_21831 (q : ℕ) :
    syracuseStep^[15] (21831 + 33554432 * q) < 21831 + 33554432 * q := by
  have h1 : syracuseStep (21831 + 33554432 * q) = 32747 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (32747 + 50331648 * q) = 49121 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (49121 + 75497472 * q) = 36841 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (36841 + 56623104 * q) = 27631 + 42467328 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h5 : syracuseStep (27631 + 42467328 * q) = 41447 + 63700992 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (41447 + 63700992 * q) = 62171 + 95551488 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (62171 + 95551488 * q) = 93257 + 143327232 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (93257 + 143327232 * q) = 69943 + 107495424 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h9 : syracuseStep (69943 + 107495424 * q) = 104915 + 161243136 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (104915 + 161243136 * q) = 157373 + 241864704 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (157373 + 241864704 * q) = 59015 + 90699264 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h12 : syracuseStep (59015 + 90699264 * q) = 88523 + 136048896 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h13 : syracuseStep (88523 + 136048896 * q) = 132785 + 204073344 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (132785 + 204073344 * q) = 99589 + 153055008 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (99589 + 153055008 * q) = 18673 + 28697814 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_22855 (q : ℕ) :
    syracuseStep^[15] (22855 + 33554432 * q) < 22855 + 33554432 * q := by
  have h1 : syracuseStep (22855 + 33554432 * q) = 34283 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (34283 + 50331648 * q) = 51425 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (51425 + 75497472 * q) = 38569 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (38569 + 56623104 * q) = 28927 + 42467328 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h5 : syracuseStep (28927 + 42467328 * q) = 43391 + 63700992 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (43391 + 63700992 * q) = 65087 + 95551488 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (65087 + 95551488 * q) = 97631 + 143327232 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (97631 + 143327232 * q) = 146447 + 214990848 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (146447 + 214990848 * q) = 219671 + 322486272 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (219671 + 322486272 * q) = 329507 + 483729408 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (329507 + 483729408 * q) = 494261 + 725594112 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (494261 + 725594112 * q) = 46337 + 68024448 * q := by
    apply certifiedStep _ _ 5
    · omega
    · omega
  have h13 : syracuseStep (46337 + 68024448 * q) = 34753 + 51018336 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h14 : syracuseStep (34753 + 51018336 * q) = 26065 + 38263752 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (26065 + 38263752 * q) = 19549 + 28697814 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_23655 (q : ℕ) :
    syracuseStep^[15] (23655 + 33554432 * q) < 23655 + 33554432 * q := by
  have h1 : syracuseStep (23655 + 33554432 * q) = 35483 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (35483 + 50331648 * q) = 53225 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (53225 + 75497472 * q) = 39919 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (39919 + 56623104 * q) = 59879 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (59879 + 84934656 * q) = 89819 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (89819 + 127401984 * q) = 134729 + 191102976 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (134729 + 191102976 * q) = 101047 + 143327232 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h8 : syracuseStep (101047 + 143327232 * q) = 151571 + 214990848 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (151571 + 214990848 * q) = 227357 + 322486272 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (227357 + 322486272 * q) = 85259 + 120932352 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h11 : syracuseStep (85259 + 120932352 * q) = 127889 + 181398528 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (127889 + 181398528 * q) = 95917 + 136048896 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h13 : syracuseStep (95917 + 136048896 * q) = 35969 + 51018336 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h14 : syracuseStep (35969 + 51018336 * q) = 26977 + 38263752 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h15 : syracuseStep (26977 + 38263752 * q) = 20233 + 28697814 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_26983 (q : ℕ) :
    syracuseStep^[14] (26983 + 33554432 * q) < 26983 + 33554432 * q := by
  have h1 : syracuseStep (26983 + 33554432 * q) = 40475 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (40475 + 50331648 * q) = 60713 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (60713 + 75497472 * q) = 45535 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (45535 + 56623104 * q) = 68303 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (68303 + 84934656 * q) = 102455 + 127401984 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (102455 + 127401984 * q) = 153683 + 191102976 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (153683 + 191102976 * q) = 230525 + 286654464 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (230525 + 286654464 * q) = 86447 + 107495424 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h9 : syracuseStep (86447 + 107495424 * q) = 129671 + 161243136 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h10 : syracuseStep (129671 + 161243136 * q) = 194507 + 241864704 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (194507 + 241864704 * q) = 291761 + 362797056 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h12 : syracuseStep (291761 + 362797056 * q) = 218821 + 272097792 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h13 : syracuseStep (218821 + 272097792 * q) = 41029 + 51018336 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  have h14 : syracuseStep (41029 + 51018336 * q) = 7693 + 9565938 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  omega

private theorem descent_33095 (q : ℕ) :
    syracuseStep^[15] (33095 + 33554432 * q) < 33095 + 33554432 * q := by
  have h1 : syracuseStep (33095 + 33554432 * q) = 49643 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (49643 + 50331648 * q) = 74465 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (74465 + 75497472 * q) = 55849 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (55849 + 56623104 * q) = 41887 + 42467328 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h5 : syracuseStep (41887 + 42467328 * q) = 62831 + 63700992 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h6 : syracuseStep (62831 + 63700992 * q) = 94247 + 95551488 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h7 : syracuseStep (94247 + 95551488 * q) = 141371 + 143327232 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (141371 + 143327232 * q) = 212057 + 214990848 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (212057 + 214990848 * q) = 159043 + 161243136 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h10 : syracuseStep (159043 + 161243136 * q) = 238565 + 241864704 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (238565 + 241864704 * q) = 44731 + 45349632 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  have h12 : syracuseStep (44731 + 45349632 * q) = 67097 + 68024448 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h13 : syracuseStep (67097 + 68024448 * q) = 50323 + 51018336 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h14 : syracuseStep (50323 + 51018336 * q) = 75485 + 76527504 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h15 : syracuseStep (75485 + 76527504 * q) = 28307 + 28697814 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

private theorem descent_34727 (q : ℕ) :
    syracuseStep^[14] (34727 + 33554432 * q) < 34727 + 33554432 * q := by
  have h1 : syracuseStep (34727 + 33554432 * q) = 52091 + 50331648 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h2 : syracuseStep (52091 + 50331648 * q) = 78137 + 75497472 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h3 : syracuseStep (78137 + 75497472 * q) = 58603 + 56623104 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h4 : syracuseStep (58603 + 56623104 * q) = 87905 + 84934656 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h5 : syracuseStep (87905 + 84934656 * q) = 65929 + 63700992 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h6 : syracuseStep (65929 + 63700992 * q) = 49447 + 47775744 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h7 : syracuseStep (49447 + 47775744 * q) = 74171 + 71663616 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h8 : syracuseStep (74171 + 71663616 * q) = 111257 + 107495424 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h9 : syracuseStep (111257 + 107495424 * q) = 83443 + 80621568 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h10 : syracuseStep (83443 + 80621568 * q) = 125165 + 120932352 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h11 : syracuseStep (125165 + 120932352 * q) = 46937 + 45349632 * q := by
    apply certifiedStep _ _ 3
    · omega
    · omega
  have h12 : syracuseStep (46937 + 45349632 * q) = 35203 + 34012224 * q := by
    apply certifiedStep _ _ 2
    · omega
    · omega
  have h13 : syracuseStep (35203 + 34012224 * q) = 52805 + 51018336 * q := by
    apply certifiedStep _ _ 1
    · omega
    · omega
  have h14 : syracuseStep (52805 + 51018336 * q) = 9901 + 9565938 * q := by
    apply certifiedStep _ _ 4
    · omega
    · omega
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  omega

theorem solution (n : ℕ)
    (h : n % 128 = 39 ∨ n % 128 = 71 ∨ n % 128 = 103)
    (h256 : n % 256 ≠ 39 ∧ n % 256 ≠ 199)
    (h1024 : n % 1024 ≠ 423 ∧ n % 1024 ≠ 583 ∧ n % 1024 ≠ 999)
    (h4096 : n % 4096 ≠ 231 ∧ n % 4096 ≠ 615 ∧ n % 4096 ≠ 935 ∧ n % 4096 ≠ 1703 ∧ n % 4096 ≠ 3143 ∧ n % 4096 ≠ 3559 ∧ n % 4096 ≠ 3911)
    (h8192 : n % 8192 ∉ ({679, 1191, 2663, 3687, 4199, 4455, 5191, 5607, 5959, 6215,
      6375, 6631, 6983, 7079, 7399, 7495, 7847, 7911, 8103} : Finset ℕ))
    (h32768 : n % 32768 ∉ ({839, 1095, 2119, 2279, 2727, 2983, 3303, 4007, 6503, 6759,
      7783, 9959, 10055, 11079, 11943, 12967, 14439, 16743, 16871, 17735,
      17767, 19623, 20199, 21223, 23399, 24647, 24679, 25703, 25831, 26087,
      26535, 27111, 27975, 28999, 29863, 30311, 30887} : Finset ℕ))
    (h65536 : n % 65536 ∉ ({359, 1351, 2407, 2791, 2887, 3239, 3815, 4775, 5863, 6247,
      7015, 8263, 8551, 9319, 9543, 10151, 10727, 11431, 12007, 12615,
      12775, 13671, 13927, 14503, 15207, 16455, 17127, 17223, 17479, 17511,
      18343, 18919, 19111, 19367, 19687, 20807, 21735, 22119, 22695, 22887,
      23143, 25415, 25671, 26343, 26439, 27303, 27559, 27879, 28327, 31079,
      31335, 33255, 34151, 34535, 34631, 36519, 37607, 37735, 40039, 41063,
      41447, 42215, 42343, 42471, 43111, 43335, 44359, 45223, 45799, 46247,
      46407, 48295, 49255, 50407, 50663, 51271, 51431, 52071, 52551, 53159,
      53319, 54375, 54439, 55207, 56935, 57671, 58983, 59463, 59559, 59623,
      60231, 61351, 62119, 62279, 63335, 63591, 64167, 64871, 65127} : Finset ℕ))
    (h524288 : n % 524288 ∉ ({
          6055, 12199, 13031, 17639, 20391, 20551, 24423, 25447, 26695, 26855, 27495, 30055, 30567,
          31591, 32103, 35175, 39783, 41319, 55463, 59719, 60071, 62791, 68935, 69287, 74215,
          77127, 80999, 83431, 84071, 87143, 88167, 91751, 96359, 97895, 109287, 112359, 115431,
          116455, 116647, 120039, 124647, 125863, 126183, 133991, 136039, 140647, 151719, 154791,
          157863, 158887, 162119, 162471, 164167, 167079, 168263, 168615, 168775, 172871, 173383,
          176455, 176615, 181063, 182087, 182759, 187495, 190279, 190567, 196711, 204903, 215783,
          218855, 219047, 224999, 225191, 225351, 229447, 233191, 235367, 236903, 237639, 238663,
          239975, 243047, 244071, 244583, 246855, 252263, 258215, 261287, 267431, 270663, 272711,
          275271, 275623, 275783, 281415, 281927, 289607, 289895, 291943, 296039, 296551, 300647,
          301159, 304231, 308839, 309863, 318055, 318183, 320231, 324327, 324839, 328935, 329447,
          331847, 332519, 337127, 337991, 338151, 340839, 341863, 343399, 346183, 346343, 346471,
          346983, 352615, 360615, 360807, 362663, 366759, 367271, 371367, 371879, 374951, 379559,
          380583, 381255, 381415, 385511, 385863, 388775, 393703, 394727, 395079, 398439, 400487,
          402919, 403047, 403559, 409191, 409703, 417383, 423847, 426727, 427943, 428775, 431335,
          431847, 436135, 437159, 437479, 437991, 442439, 444263, 445351, 445671, 445799, 447335,
          447847, 451655, 451943, 457063, 460135, 469159, 471207, 473767, 474279, 477511, 479911,
          480423, 480583, 483655, 484679, 487911, 488103, 488263, 492871, 494055, 494407, 502247,
          509031, 513639, 522855
        } : Finset ℕ))
    (h1048576 : n % 1048576 ∉ ({
          5287, 8519, 10567, 13479, 13639, 19783, 27751, 29799, 33895, 39015, 42087, 56039, 58087,
          62183, 67303, 70375, 81255, 84327, 90471, 98663, 105127, 109223, 117415, 118439, 123719,
          126631, 132935, 140903, 147047, 155239, 161703, 165799, 169191, 173991, 175015, 175335,
          180295, 182119, 183207, 183527, 185191, 189511, 207015, 209063, 212135, 215367, 218279,
          218439, 221511, 222535, 225767, 230727, 231911, 240103, 246887, 275175, 292199, 294247,
          297319, 303463, 322215, 331431, 353895, 360039, 378791, 382183, 388007, 388327, 396135,
          398183, 413863, 416935, 420007, 421031, 424263, 426311, 429223, 430407, 435527, 438599,
          438759, 444903, 449639, 452711, 458855, 467047, 477927, 480999, 487143, 495335, 499047,
          502119, 505191, 506215, 514407, 537415, 543559, 551751, 558695, 562791, 570983, 572007,
          580199, 586983, 591079, 593991, 599271, 600135, 600295, 602983, 604007, 608327, 608487,
          609127, 622759, 624807, 628903, 634023, 637095, 643399, 643559, 647655, 655847, 656871,
          660583, 662631, 665063, 665703, 671847, 688871, 690919, 693991, 700135, 707943, 709991,
          714087, 719207, 722279, 735911, 742055, 750247, 750407, 756551, 775783, 784999, 792487,
          798631, 804071, 806823, 806983, 810855, 811879, 813127, 813287, 813927, 816999, 818023,
          826215, 841895, 846151, 849223, 855367, 860647, 863559, 867431, 869863, 870503, 873575,
          874599, 882791, 895719, 898791, 901863, 902887, 911079, 927079, 948903, 955047, 955207,
          959303, 967495, 968519, 976711, 1005479, 1011623, 1011783, 1015879, 1021799, 1024071,
          1025095, 1031015, 1033287, 1044647, 1047719
        } : Finset ℕ))
    (h21_11 : n % 2097152 ∉ syracuseSevenMod32New21Step11Classes)
    (h21_12 : n % 2097152 ∉ syracuseSevenMod32New21Step12Classes)
    (h22_11 : n % 4194304 ∉ syracuseSevenMod32New22Step11Classes)
    (h22_12 : n % 4194304 ∉ syracuseSevenMod32New22Step12Classes)
    (h22_13 : n % 4194304 ∉ syracuseSevenMod32New22Step13Classes)
    (h23_11_01 : n % 8388608 ∉ syracuseSevenMod32New23Step11Chunk01Classes)
    (h23_12_01 : n % 8388608 ∉ syracuseSevenMod32New23Step12Chunk01Classes)
    (h23_13_01 : n % 8388608 ∉ syracuseSevenMod32New23Step13Chunk01Classes)
    (h23_13_02 : n % 8388608 ∉ syracuseSevenMod32New23Step13Chunk02Classes)
    (h24_11_01 : n % 16777216 ∉ syracuseSevenMod32New24Step11Chunk01Classes)
    (h24_12_01 : n % 16777216 ∉ syracuseSevenMod32New24Step12Chunk01Classes)
    (h24_13_01 : n % 16777216 ∉ syracuseSevenMod32New24Step13Chunk01Classes)
    (h24_13_02 : n % 16777216 ∉ syracuseSevenMod32New24Step13Chunk02Classes)
    (h24_14_01 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk01Classes)
    (h24_14_02 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk02Classes)
    (h24_14_03 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk03Classes)
    (h24_14_04 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk04Classes)
    (h24_14_05 : n % 16777216 ∉ syracuseSevenMod32New24Step14Chunk05Classes) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hs : n < 2310000
  · have hn : 1 < n := by rcases h with h | h | h <;> omega
    have ho : Odd n := Nat.odd_iff.mpr (by rcases h with h | h | h <;> omega)
    exact syracuse_descends_below_2310000 n hn hs ho
  by_cases hc : n % 33554432 ∈ ([743, 4839, 5735, 7335, 9287, 9575, 11495, 14247, 15975, 16231, 21831, 22855, 23655, 26983, 33095, 34727] : List ℕ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
    · have he : n = 743 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_743 (n / 33554432)⟩
    · have he : n = 4839 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_4839 (n / 33554432)⟩
    · have he : n = 5735 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_5735 (n / 33554432)⟩
    · have he : n = 7335 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_7335 (n / 33554432)⟩
    · have he : n = 9287 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_9287 (n / 33554432)⟩
    · have he : n = 9575 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_9575 (n / 33554432)⟩
    · have he : n = 11495 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_11495 (n / 33554432)⟩
    · have he : n = 14247 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_14247 (n / 33554432)⟩
    · have he : n = 15975 + 33554432 * (n / 33554432) := by omega
      exact ⟨14, he.symm ▸ descent_15975 (n / 33554432)⟩
    · have he : n = 16231 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_16231 (n / 33554432)⟩
    · have he : n = 21831 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_21831 (n / 33554432)⟩
    · have he : n = 22855 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_22855 (n / 33554432)⟩
    · have he : n = 23655 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_23655 (n / 33554432)⟩
    · have he : n = 26983 + 33554432 * (n / 33554432) := by omega
      exact ⟨14, he.symm ▸ descent_26983 (n / 33554432)⟩
    · have he : n = 33095 + 33554432 * (n / 33554432) := by omega
      exact ⟨15, he.symm ▸ descent_33095 (n / 33554432)⟩
    · have he : n = 34727 + 33554432 * (n / 33554432) := by omega
      exact ⟨14, he.symm ▸ descent_34727 (n / 33554432)⟩
  · exact syracuse_descent_residual_seven_mod32_mod16777216_refined n h h256 h1024 h4096 h8192 h32768 h65536 h524288 h1048576 h21_11 h21_12 h22_11 h22_12 h22_13 h23_11_01 h23_12_01 h23_13_01 h23_13_02 h24_11_01 h24_12_01 h24_13_01 h24_13_02 h24_14_01 h24_14_02 h24_14_03 h24_14_04 h24_14_05 (by omega) hc
