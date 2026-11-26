-- Prove2me | solution 1 for syracuse_descent_coprime_to_six_combined_20971520_to_423624704
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:31:14.826324+00:00
-- url     : https://prove2.me/submissions/58fbd71e-a419-4fb8-9d5b-cfe86f8f2dcf

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_syracuse_descent_coprime_to_six_20971520_to_33554432
import Theorems.Thm_syracuse_descent_coprime_to_six_33554432_to_46137344
import Theorems.Thm_syracuse_descent_coprime_to_six_46137344_to_58720256
import Theorems.Thm_syracuse_descent_coprime_to_six_58720256_to_71303168
import Theorems.Thm_syracuse_descent_coprime_to_six_71303168_to_83886080
import Theorems.Thm_syracuse_descent_coprime_to_six_83886080_to_96468992
import Theorems.Thm_syracuse_descent_coprime_to_six_96468992_to_109051904
import Theorems.Thm_syracuse_descent_coprime_to_six_109051904_to_121634816
import Theorems.Thm_syracuse_descent_coprime_to_six_121634816_to_134217728
import Theorems.Thm_syracuse_descent_coprime_to_six_134217728_to_146800640
import Theorems.Thm_syracuse_descent_coprime_to_six_146800640_to_159383552
import Theorems.Thm_syracuse_descent_coprime_to_six_159383552_to_171966464
import Theorems.Thm_syracuse_descent_coprime_to_six_171966464_to_184549376
import Theorems.Thm_syracuse_descent_coprime_to_six_184549376_to_197132288
import Theorems.Thm_syracuse_descent_coprime_to_six_197132288_to_209715200
import Theorems.Thm_syracuse_descent_coprime_to_six_209715200_to_222298112
import Theorems.Thm_syracuse_descent_coprime_to_six_222298112_to_234881024
import Theorems.Thm_syracuse_descent_coprime_to_six_234881024_to_247463936
import Theorems.Thm_syracuse_descent_coprime_to_six_247463936_to_260046848
import Theorems.Thm_syracuse_descent_coprime_to_six_260046848_to_272629760
import Theorems.Thm_syracuse_descent_coprime_to_six_272629760_to_285212672
import Theorems.Thm_syracuse_descent_coprime_to_six_285212672_to_297795584
import Theorems.Thm_syracuse_descent_coprime_to_six_297795584_to_310378496
import Theorems.Thm_syracuse_descent_coprime_to_six_310378496_to_322961408
import Theorems.Thm_syracuse_descent_coprime_to_six_322961408_to_335544320
import Theorems.Thm_syracuse_descent_coprime_to_six_335544320_to_348127232
import Theorems.Thm_syracuse_descent_coprime_to_six_348127232_to_360710144
import Theorems.Thm_syracuse_descent_coprime_to_six_360710144_to_373293056
import Theorems.Thm_syracuse_descent_coprime_to_six_373293056_to_385875968
import Theorems.Thm_syracuse_descent_coprime_to_six_385875968_to_398458880
import Theorems.Thm_syracuse_descent_coprime_to_six_398458880_to_411041792
import Theorems.Thm_syracuse_descent_coprime_to_six_411041792_to_423624704
set_option maxHeartbeats 0 in
theorem solution (n : ℕ) (hl : 20971520 ≤ n) (hu : n < 423624704) (ho : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  by_cases hBand1 : n < 222298112
  · by_cases hBand2 : n < 121634816
    · by_cases hBand3 : n < 71303168
      · by_cases hBand4 : n < 46137344
        · by_cases hBand5 : n < 33554432
          · exact syracuse_descent_coprime_to_six_20971520_to_33554432 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_33554432_to_46137344 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 58720256
          · exact syracuse_descent_coprime_to_six_46137344_to_58720256 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_58720256_to_71303168 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 96468992
        · by_cases hBand5 : n < 83886080
          · exact syracuse_descent_coprime_to_six_71303168_to_83886080 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_83886080_to_96468992 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 109051904
          · exact syracuse_descent_coprime_to_six_96468992_to_109051904 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_109051904_to_121634816 n (by omega) (by omega) ho h3
    · by_cases hBand3 : n < 171966464
      · by_cases hBand4 : n < 146800640
        · by_cases hBand5 : n < 134217728
          · exact syracuse_descent_coprime_to_six_121634816_to_134217728 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_134217728_to_146800640 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 159383552
          · exact syracuse_descent_coprime_to_six_146800640_to_159383552 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_159383552_to_171966464 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 197132288
        · by_cases hBand5 : n < 184549376
          · exact syracuse_descent_coprime_to_six_171966464_to_184549376 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_184549376_to_197132288 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 209715200
          · exact syracuse_descent_coprime_to_six_197132288_to_209715200 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_209715200_to_222298112 n (by omega) (by omega) ho h3
  · by_cases hBand2 : n < 322961408
    · by_cases hBand3 : n < 272629760
      · by_cases hBand4 : n < 247463936
        · by_cases hBand5 : n < 234881024
          · exact syracuse_descent_coprime_to_six_222298112_to_234881024 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_234881024_to_247463936 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 260046848
          · exact syracuse_descent_coprime_to_six_247463936_to_260046848 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_260046848_to_272629760 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 297795584
        · by_cases hBand5 : n < 285212672
          · exact syracuse_descent_coprime_to_six_272629760_to_285212672 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_285212672_to_297795584 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 310378496
          · exact syracuse_descent_coprime_to_six_297795584_to_310378496 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_310378496_to_322961408 n (by omega) (by omega) ho h3
    · by_cases hBand3 : n < 373293056
      · by_cases hBand4 : n < 348127232
        · by_cases hBand5 : n < 335544320
          · exact syracuse_descent_coprime_to_six_322961408_to_335544320 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_335544320_to_348127232 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 360710144
          · exact syracuse_descent_coprime_to_six_348127232_to_360710144 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_360710144_to_373293056 n (by omega) (by omega) ho h3
      · by_cases hBand4 : n < 398458880
        · by_cases hBand5 : n < 385875968
          · exact syracuse_descent_coprime_to_six_373293056_to_385875968 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_385875968_to_398458880 n (by omega) (by omega) ho h3
        · by_cases hBand5 : n < 411041792
          · exact syracuse_descent_coprime_to_six_398458880_to_411041792 n (by omega) (by omega) ho h3
          · exact syracuse_descent_coprime_to_six_411041792_to_423624704 n (by omega) (by omega) ho h3
