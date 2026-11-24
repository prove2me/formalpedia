-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_sum_Ico_tsub_telescope
-- name    : Formalism.GradedWeylDivisibility.sum_Ico_tsub_telescope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:04.730877+00:00
-- url     : https://prove2.me/theorems/74fa6bcc-0d96-44e7-8e2e-d649fadf2f5c
-- title:
--   Graded Weyl Divisibility: sum Ico tsub telescope
-- statement:
--   The Graded Weyl Divisibility construction uses the sum Ico tsub telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean#L11-L24

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.sum_Ico_tsub_telescope (g : ℕ → ℕ) (n : ℕ) (hg : ∀ i, g (i + 1) ≤ g i)
    (hn : ∀ i, n ≤ i → g i = 0) :
    ∀ d k, n - k = d → ∑ i ∈ Finset.Ico k n, (g i - g (i + 1)) = g k := by sorry
