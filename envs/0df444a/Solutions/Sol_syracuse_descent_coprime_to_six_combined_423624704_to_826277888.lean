-- Prove2me | solution 1 for syracuse_descent_coprime_to_six_combined_423624704_to_826277888
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:31:15.633183+00:00
-- url     : https://prove2.me/submissions/bbf07146-abf0-49ea-b086-e6dd5a99fff1

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_syracuse_descent_coprime_to_six_423624704_to_436207616
import Theorems.Thm_syracuse_descent_coprime_to_six_436207616_to_448790528
import Theorems.Thm_syracuse_descent_coprime_to_six_448790528_to_461373440
import Theorems.Thm_syracuse_descent_coprime_to_six_461373440_to_473956352
import Theorems.Thm_syracuse_descent_coprime_to_six_473956352_to_486539264
import Theorems.Thm_syracuse_descent_coprime_to_six_486539264_to_499122176
import Theorems.Thm_syracuse_descent_coprime_to_six_499122176_to_511705088
import Theorems.Thm_syracuse_descent_coprime_to_six_511705088_to_524288000
import Theorems.Thm_syracuse_descent_coprime_to_six_524288000_to_536870912
import Theorems.Thm_syracuse_descent_coprime_to_six_536870912_to_549453824
import Theorems.Thm_syracuse_descent_coprime_to_six_549453824_to_562036736
import Theorems.Thm_syracuse_descent_coprime_to_six_562036736_to_574619648
import Theorems.Thm_syracuse_descent_coprime_to_six_574619648_to_587202560
import Theorems.Thm_syracuse_descent_coprime_to_six_587202560_to_599785472
import Theorems.Thm_syracuse_descent_coprime_to_six_599785472_to_612368384
import Theorems.Thm_syracuse_descent_coprime_to_six_612368384_to_624951296
import Theorems.Thm_syracuse_descent_coprime_to_six_624951296_to_637534208
import Theorems.Thm_syracuse_descent_coprime_to_six_637534208_to_650117120
import Theorems.Thm_syracuse_descent_coprime_to_six_650117120_to_662700032
import Theorems.Thm_syracuse_descent_coprime_to_six_662700032_to_675282944
import Theorems.Thm_syracuse_descent_coprime_to_six_675282944_to_687865856
import Theorems.Thm_syracuse_descent_coprime_to_six_687865856_to_700448768
import Theorems.Thm_syracuse_descent_coprime_to_six_700448768_to_713031680
import Theorems.Thm_syracuse_descent_coprime_to_six_713031680_to_725614592
import Theorems.Thm_syracuse_descent_coprime_to_six_725614592_to_738197504
import Theorems.Thm_syracuse_descent_coprime_to_six_738197504_to_750780416
import Theorems.Thm_syracuse_descent_coprime_to_six_750780416_to_763363328
import Theorems.Thm_syracuse_descent_coprime_to_six_763363328_to_775946240
import Theorems.Thm_syracuse_descent_coprime_to_six_775946240_to_788529152
import Theorems.Thm_syracuse_descent_coprime_to_six_788529152_to_801112064
import Theorems.Thm_syracuse_descent_coprime_to_six_801112064_to_813694976
import Theorems.Thm_syracuse_descent_coprime_to_six_813694976_to_826277888
set_option maxHeartbeats 0 in
theorem solution (n : ℕ) (hl : 423624704 ≤ n) (hu : n < 826277888) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hBand1 : n < 624951296
  · by_cases hBand2 : n < 524288000
    · by_cases hBand3 : n < 473956352
      · by_cases hBand4 : n < 448790528
        · by_cases hBand5 : n < 436207616
          · exact syracuse_descent_coprime_to_six_423624704_to_436207616 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_436207616_to_448790528 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 461373440
          · exact syracuse_descent_coprime_to_six_448790528_to_461373440 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_461373440_to_473956352 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 499122176
        · by_cases hBand5 : n < 486539264
          · exact syracuse_descent_coprime_to_six_473956352_to_486539264 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_486539264_to_499122176 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 511705088
          · exact syracuse_descent_coprime_to_six_499122176_to_511705088 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_511705088_to_524288000 n (by omega) (by omega) ho h3
    · by_cases hBand3 : n < 574619648
      · by_cases hBand4 : n < 549453824
        · by_cases hBand5 : n < 536870912
          · exact syracuse_descent_coprime_to_six_524288000_to_536870912 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_536870912_to_549453824 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 562036736
          · exact syracuse_descent_coprime_to_six_549453824_to_562036736 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_562036736_to_574619648 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 599785472
        · by_cases hBand5 : n < 587202560
          · exact syracuse_descent_coprime_to_six_574619648_to_587202560 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_587202560_to_599785472 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 612368384
          · exact syracuse_descent_coprime_to_six_599785472_to_612368384 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_612368384_to_624951296 n (by omega) (by omega) ho h3
  · by_cases hBand2 : n < 725614592
    · by_cases hBand3 : n < 675282944
      · by_cases hBand4 : n < 650117120
        · by_cases hBand5 : n < 637534208
          · exact syracuse_descent_coprime_to_six_624951296_to_637534208 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_637534208_to_650117120 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 662700032
          · exact syracuse_descent_coprime_to_six_650117120_to_662700032 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_662700032_to_675282944 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 700448768
        · by_cases hBand5 : n < 687865856
          · exact syracuse_descent_coprime_to_six_675282944_to_687865856 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_687865856_to_700448768 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 713031680
          · exact syracuse_descent_coprime_to_six_700448768_to_713031680 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_713031680_to_725614592 n (by omega) (by omega) ho h3
    · by_cases hBand3 : n < 775946240
      · by_cases hBand4 : n < 750780416
        · by_cases hBand5 : n < 738197504
          · exact syracuse_descent_coprime_to_six_725614592_to_738197504 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_738197504_to_750780416 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 763363328
          · exact syracuse_descent_coprime_to_six_750780416_to_763363328 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_763363328_to_775946240 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 801112064
        · by_cases hBand5 : n < 788529152
          · exact syracuse_descent_coprime_to_six_775946240_to_788529152 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_788529152_to_801112064 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 813694976
          · exact syracuse_descent_coprime_to_six_801112064_to_813694976 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_813694976_to_826277888 n (by omega) (by omega) ho h3
