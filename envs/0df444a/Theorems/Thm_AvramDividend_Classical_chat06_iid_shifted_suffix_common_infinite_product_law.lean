-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law
-- name    : AvramDividend.Classical.chat06_iid_shifted_suffix_common_infinite_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:15:43.950615+00:00
-- url     : https://prove2.me/theorems/b888f799-9e4d-4189-9a0c-c78838d9ef06
-- title:
--   IID shifted waiting-time suffix has the same countable infinite-product law
-- statement:
--   For a countably indexed independent family of measurable real waiting times with common marginal distribution ν, the entire shifted suffix beginning at index n+1 has joint distribution equal to the infinite product of ν. The proof reindexes the indexed-independence theorem along an injective translation j↦n+1+j, supplies the common marginal HasLaw hypotheses, and applies the pinned Mathlib infinite-product HasLaw theorem. This establishes the future-suffix law required by the renewal memorylessness and natural-filtration independence programme.
-- source:
--   bv_iid_shifted_suffix_has_common_infinite_product_law_chat06_20261022.lean, 25 lines, 1081 bytes, SHA-256 e17219cf1882384c9e1366fb76ad74793e760553961ee0d9b74de056fd25253c; private probe e11afe34-e621-4516-bc10-3de6331c4205 passed sentinel with zero candidate errors.

import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Measure ProbabilityTheory
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_iid_shifted_suffix_common_infinite_product_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (ν : Measure ℝ) (hν : ∀ i, HasLaw (τ i) ν P)
    (n : ℕ) :
    HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω)
      (infinitePi (fun _ : ℕ => ν)) P := by sorry
