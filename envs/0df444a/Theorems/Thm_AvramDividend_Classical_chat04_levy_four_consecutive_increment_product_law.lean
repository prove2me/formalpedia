-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_levy_four_consecutive_increment_product_law
-- name    : AvramDividend.Classical.chat04_levy_four_consecutive_increment_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:21:47.848994+00:00
-- url     : https://prove2.me/theorems/fb9844ed-0399-4081-b33c-ffad0c42d510
-- title:
--   Four consecutive Lévy state and increment components have the product joint law
-- statement:
--   For ordered deterministic times s≤t≤u≤v, prove the exact joint product measure of (X_s, X_t−X_s, X_u−X_t, X_v−X_u) is the nested four-factor product Law(X_s)⊗Law(X_(t−s))⊗Law(X_(u−t))⊗Law(X_(v−u)). Crucially the new last increment is independent of the entire filtration F_u. Since the earlier three-component vector is adapted to F_u, its sigma algebra is a subalgebra, hence independent of the new increment. Apply pinned Mathlib IndepFun.map_prod_eq_prod_map_map to factor the joint law and use the already accepted three-consecutive-increment law and stationary increments for the marginals. This advances finite-grid path distribution factorisation; it does not imply continuous-time killed scale martingality or rule out inter-grid ruin.
-- source:
--   Accepted Chat04 three consecutive product joint law adf6e5bb-a491-49b4-88bc-4836ec017ebd, original SpectrallyNegativeLevy adapted, full-past independent and stationary increments; pinned Mathlib ProbabilityTheory.IndepFun_iff_Indep and IndepFun.map_prod_eq_prod_map_map.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_three_consecutive_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_levy_four_consecutive_increment_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    Measure.map
      (fun ω => (((X.X s ω, X.X t ω - X.X s ω),
         X.X u ω - X.X t ω), X.X v ω - X.X u ω)) P =
      (((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P)).prod
          (Measure.map (X.X (v - u)) P) := by sorry
