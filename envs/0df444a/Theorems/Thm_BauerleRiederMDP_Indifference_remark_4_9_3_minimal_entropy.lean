-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_remark_4_9_3_minimal_entropy
-- name    : BauerleRiederMDP.Indifference.remark_4_9_3_minimal_entropy
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:28:46.933693+00:00
-- url     : https://prove2.me/theorems/db31d32c-cd80-4eaf-b5da-9ba7995ecf88
-- title:
--   Remark 4.9.3 — $\mathbb Q$ is the minimal entropy martingale measure
-- statement:
--   The measure $\mathbb Q$ of Remark 4.9.3 is the minimal entropy martingale measure: it is an equivalent martingale measure, and it solves
--   $$
--   \min_{Q'}\ \mathbb E_{Q'}\Bigl[\log\frac{dQ'}{d\mathbb P}\Bigr],
--   $$
--   where the minimum is taken over all $\mathbb P$-equivalent measures which satisfy $\mathbb E_{Q'}S_1=S_0$.
--
--   This singles out $\mathbb Q$ among the infinitely many equivalent martingale measures of the incomplete one-period market.
--
--   Differences from the source: none.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 4.9.3, p.137

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_Q
import Definitions.Def_BauerleRiederMDP_Indifference_Market_IsEMM
import Definitions.Def_BauerleRiederMDP_Indifference_Market_entropy

namespace BauerleRiederMDP.Indifference

/-- Remark 4.9.3, minimal entropy (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), Remark 4.9.3, p.137, PDF 151). `ℚ` is the minimal entropy martingale measure: it
solves `min_ℚ 𝔼_ℚ[log dℚ/dℙ]`, the minimum being taken over all equivalent martingale measures. -/
theorem remark_4_9_3_minimal_entropy (M : Market) :
    M.IsEMM M.Q ∧ ∀ Q' : MeasureTheory.Measure (Fin 4), M.IsEMM Q' →
      M.entropy M.Q ≤ M.entropy Q' := by sorry

end BauerleRiederMDP.Indifference
