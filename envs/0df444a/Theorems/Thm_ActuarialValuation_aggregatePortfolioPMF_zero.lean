-- Prove2me | Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_zero
-- name    : ActuarialValuation.aggregatePortfolioPMF_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:34:26.38499+00:00
-- url     : https://prove2.me/theorems/89bdf4e6-1162-499d-b642-5f0e7c3e1223
-- title:
--   A zero-policy portfolio has certain zero aggregate loss
-- statement:
--   Without any insured policies, no claim event can generate a positive loss. The initial aggregate distribution is therefore one at loss zero and zero for all positive integer losses, independently of hypothetical claim parameters.
--
--   **Mathematical statement**
--
--   $$
--   g_0(s)=\mathbf1_{\{s=0\}}
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF

namespace ActuarialValuation

theorem aggregatePortfolioPMF_zero (p : ℕ → ℝ) (b : ℕ → ℕ) (s : ℕ) :
  aggregatePortfolioPMF p b 0 s = (if s = 0 then 1 else 0) := by sorry

end ActuarialValuation
