-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffVariance_shift
-- name    : ActuarialValuation.finiteHattendorffVariance_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:22:46.445232+00:00
-- url     : https://prove2.me/theorems/de166859-7535-4382-a986-ed26a5d56242
-- title:
--   Finite-scenario variance invariant under a constant cash shift
-- statement:
--   Under unit total scenario mass, adding the same deterministic amount to each realised loss does not change its weighted second central moment.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(c+X)=\operatorname{Var}_w(X)
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityVariance

namespace ActuarialValuation

theorem finiteHattendorffVariance_shift {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
  (hsum : (∑ ω : Ω, w ω) = 1)
  :
  finiteMortalityVariance w (fun ω => c + X ω) = finiteMortalityVariance w X := by sorry

end ActuarialValuation
