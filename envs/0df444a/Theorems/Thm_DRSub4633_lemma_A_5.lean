-- Prove2me | Theorems.Thm_DRSub4633_lemma_A_5
-- name    : DRSub4633.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:10:06.661982+00:00
-- url     : https://prove2.me/theorems/921aa822-2302-45aa-9345-1f200c85d75e
-- title:
--   Lemma A.5 — boundary estimates
-- statement:
--   The budget $B$ is nonnegative on $[0,1]$, and
--   $$B(t)\ge I(t):=\int_t^1[c_1w(r)-\Gamma]\,dr\qquad(t_0\le t\le 1).\tag{127}$$
--   Moreover
--   $$B(t)\ge B(t_0)>\frac{527511}{8000000}>\frac{21}{320}\qquad(t_0\le t\le t_1).\tag{128}$$
--
--   Differences from the source: none.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.5, p.48

import Mathlib
import Definitions.Def_DRSub4633_Bbudget
import Definitions.Def_DRSub4633_Itail
import Definitions.Def_DRSub4633_t0
import Definitions.Def_DRSub4633_t1

namespace DRSub4633

/-- **Lemma A.5 (Boundary estimates).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.5, p.48: "The function `B` is
nonnegative on `[0, 1]`, and `B(t) ≥ I(t) := ∫_t^1 [c₁w(r) − Γ] dr` (`t₀ ≤ t ≤ 1`). (127) Moreover,
`B(t) ≥ B(t₀) > 527511/8000000 > 21/320` (`t₀ ≤ t ≤ t₁`). (128)" -/
theorem lemma_A_5 :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Bbudget t) ∧
    (∀ t ∈ Set.Icc t0 1, Itail t ≤ Bbudget t) ∧
    (∀ t ∈ Set.Icc t0 t1, Bbudget t0 ≤ Bbudget t) ∧
    (527511 / 8000000 : ℝ) < Bbudget t0 ∧ (21 / 320 : ℝ) < 527511 / 8000000 := by sorry

end DRSub4633
