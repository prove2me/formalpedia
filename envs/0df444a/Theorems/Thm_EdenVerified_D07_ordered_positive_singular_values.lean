-- Prove2me | Theorems.Thm_EdenVerified_D07_ordered_positive_singular_values
-- name    : EdenVerified.D07_ordered_positive_singular_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:26:26.119823+00:00
-- url     : https://prove2.me/theorems/2b037b5b-005c-5e65-9283-330c1323826f
-- title:
--   Eden Verified: D07 ordered positive singular values
-- statement:
--   Standard singular values of the full ambient derivative.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L580-L591
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L580-L591

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D07_ordered_positive_singular_values (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) ∧
    Antitone (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (∀ i : Fin 5, 0 < (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (derivativeFactors c t p)) := by sorry
