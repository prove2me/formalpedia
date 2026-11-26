-- Prove2me | solution 1 for syracuse_descent_coprime_to_six_combined_826277888_to_1241513984
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:31:16.635784+00:00
-- url     : https://prove2.me/submissions/1210d5bc-cd56-422b-b145-b7b348326aed

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_syracuse_descent_coprime_to_six_826277888_to_838860800
import Theorems.Thm_syracuse_descent_coprime_to_six_838860800_to_851443712
import Theorems.Thm_syracuse_descent_coprime_to_six_851443712_to_864026624
import Theorems.Thm_syracuse_descent_coprime_to_six_864026624_to_876609536
import Theorems.Thm_syracuse_descent_coprime_to_six_876609536_to_889192448
import Theorems.Thm_syracuse_descent_coprime_to_six_889192448_to_901775360
import Theorems.Thm_syracuse_descent_coprime_to_six_901775360_to_914358272
import Theorems.Thm_syracuse_descent_coprime_to_six_914358272_to_926941184
import Theorems.Thm_syracuse_descent_coprime_to_six_926941184_to_939524096
import Theorems.Thm_syracuse_descent_coprime_to_six_939524096_to_952107008
import Theorems.Thm_syracuse_descent_coprime_to_six_952107008_to_964689920
import Theorems.Thm_syracuse_descent_coprime_to_six_964689920_to_977272832
import Theorems.Thm_syracuse_descent_coprime_to_six_977272832_to_989855744
import Theorems.Thm_syracuse_descent_coprime_to_six_989855744_to_1002438656
import Theorems.Thm_syracuse_descent_coprime_to_six_1002438656_to_1015021568
import Theorems.Thm_syracuse_descent_coprime_to_six_1015021568_to_1027604480
import Theorems.Thm_syracuse_descent_coprime_to_six_1027604480_to_1040187392
import Theorems.Thm_syracuse_descent_coprime_to_six_1040187392_to_1052770304
import Theorems.Thm_syracuse_descent_coprime_to_six_1052770304_to_1065353216
import Theorems.Thm_syracuse_descent_coprime_to_six_1065353216_to_1077936128
import Theorems.Thm_syracuse_descent_coprime_to_six_1077936128_to_1090519040
import Theorems.Thm_syracuse_descent_coprime_to_six_1090519040_to_1103101952
import Theorems.Thm_syracuse_descent_coprime_to_six_1103101952_to_1115684864
import Theorems.Thm_syracuse_descent_coprime_to_six_1115684864_to_1128267776
import Theorems.Thm_syracuse_descent_coprime_to_six_1128267776_to_1140850688
import Theorems.Thm_syracuse_descent_coprime_to_six_1140850688_to_1153433600
import Theorems.Thm_syracuse_descent_coprime_to_six_1153433600_to_1166016512
import Theorems.Thm_syracuse_descent_coprime_to_six_1166016512_to_1178599424
import Theorems.Thm_syracuse_descent_coprime_to_six_1178599424_to_1191182336
import Theorems.Thm_syracuse_descent_coprime_to_six_1191182336_to_1203765248
import Theorems.Thm_syracuse_descent_coprime_to_six_1203765248_to_1216348160
import Theorems.Thm_syracuse_descent_coprime_to_six_1216348160_to_1228931072
import Theorems.Thm_syracuse_descent_coprime_to_six_1228931072_to_1241513984
set_option maxHeartbeats 0 in
theorem solution (n : ℕ) (hl : 826277888 ≤ n) (hu : n < 1241513984) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hBand1 : n < 1027604480
  · by_cases hBand2 : n < 926941184
    · by_cases hBand3 : n < 876609536
      · by_cases hBand4 : n < 851443712
        · by_cases hBand5 : n < 838860800
          · exact syracuse_descent_coprime_to_six_826277888_to_838860800 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_838860800_to_851443712 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 864026624
          · exact syracuse_descent_coprime_to_six_851443712_to_864026624 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_864026624_to_876609536 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 901775360
        · by_cases hBand5 : n < 889192448
          · exact syracuse_descent_coprime_to_six_876609536_to_889192448 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_889192448_to_901775360 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 914358272
          · exact syracuse_descent_coprime_to_six_901775360_to_914358272 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_914358272_to_926941184 n (by omega) (by omega) ho h3
    · by_cases hBand3 : n < 977272832
      · by_cases hBand4 : n < 952107008
        · by_cases hBand5 : n < 939524096
          · exact syracuse_descent_coprime_to_six_926941184_to_939524096 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_939524096_to_952107008 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 964689920
          · exact syracuse_descent_coprime_to_six_952107008_to_964689920 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_964689920_to_977272832 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 1002438656
        · by_cases hBand5 : n < 989855744
          · exact syracuse_descent_coprime_to_six_977272832_to_989855744 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_989855744_to_1002438656 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 1015021568
          · exact syracuse_descent_coprime_to_six_1002438656_to_1015021568 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1015021568_to_1027604480 n (by omega) (by omega) ho h3
  · by_cases hBand2 : n < 1128267776
    · by_cases hBand3 : n < 1077936128
      · by_cases hBand4 : n < 1052770304
        · by_cases hBand5 : n < 1040187392
          · exact syracuse_descent_coprime_to_six_1027604480_to_1040187392 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1040187392_to_1052770304 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 1065353216
          · exact syracuse_descent_coprime_to_six_1052770304_to_1065353216 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1065353216_to_1077936128 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 1103101952
        · by_cases hBand5 : n < 1090519040
          · exact syracuse_descent_coprime_to_six_1077936128_to_1090519040 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1090519040_to_1103101952 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 1115684864
          · exact syracuse_descent_coprime_to_six_1103101952_to_1115684864 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1115684864_to_1128267776 n (by omega) (by omega) ho h3
    · by_cases hBand3 : n < 1178599424
      · by_cases hBand4 : n < 1153433600
        · by_cases hBand5 : n < 1140850688
          · exact syracuse_descent_coprime_to_six_1128267776_to_1140850688 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1140850688_to_1153433600 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 1166016512
          · exact syracuse_descent_coprime_to_six_1153433600_to_1166016512 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1166016512_to_1178599424 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 1203765248
        · by_cases hBand5 : n < 1191182336
          · exact syracuse_descent_coprime_to_six_1178599424_to_1191182336 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_1191182336_to_1203765248 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 1216348160
          · exact syracuse_descent_coprime_to_six_1203765248_to_1216348160 n (by omega) (by omega) ho h3
          · by_cases hBand6 : n < 1228931072
            · exact syracuse_descent_coprime_to_six_1216348160_to_1228931072 n (by omega) (by omega) ho h3
            · exact syracuse_descent_coprime_to_six_1228931072_to_1241513984 n (by omega) (by omega) ho h3
