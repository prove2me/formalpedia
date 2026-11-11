-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_lemma_B_9
-- name    : BetterKMedian.LMPGreedy.lemma_B_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:57.958258+00:00
-- url     : https://prove2.me/theorems/30d8241c-512d-45d4-97cd-1b3a48b7ef40
-- title:
--   Lemma B.9 — correct admissible advice exists
-- statement:
--   Fix $n\ge2$, $\gamma\in(1,1.224]$ and first bidding times $\tau_j\in\{j,\dots,n\}$. There is an admissible advice $\Gamma$ (Definition B.6 and Property B.7) for which the profile constructed in Section B.3 satisfies $R_0=\sum_{k=1}^n\hat g_k=1$.
--
--   Differences from the source:
--   - encoding: first bidding times τ_j ∈ {j, …, n} for every client j → `τ : ℕ → ℕ` with `ValidTau n τ` (j ≤ τ j ≤ n for 1 ≤ j ≤ n); values at other indices unused; reason: same choices of τ
--   - encoding: advice Γ = (T⋆, {µ⋆_j}_{τ_j = T⋆}, ĝ⋆_n when T⋆ = n) (Definition B.6) → `Γ : Advice` with fields `T`, `mu : ℕ → ℝ`, `gn : ℝ`; entries the construction does not use are ignored; `Advice.IsAdmissible n τ Γ` is Definition B.6 with Property B.7; reason: same advice
--   - encoding: the procedure of Section B.3 (memberships (23), Algorithm 2 with (24), (25), Table 2 and (26)) → `ghat`, `gCert`, `sCert`, `tCert`, `Rsuf` of `Def_BetterKMedian_LMPGreedy_DualCertificate`, functions of (n, γ, τ, Γ); "returns ⊥ unless R_0 = 1" is the hypothesis `Rsuf n γ τ Γ 0 = 1`; reason: same construction; Lean division by 0 is 0 but every denominator is positive in this parameter range (proof of Lemma B.11)
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Lemma B.9, printed p. 42 (PDF 44)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_FRPrimalDual
import Definitions.Def_BetterKMedian_LMPGreedy_DualCertificate

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Lemma B.9** (Buhai et al. 2026, printed p. 42, PDF 44). Fix `n ≥ 2`, `γ ∈ (1, 1.224]` and
first bidding times `τ_j ∈ {j, …, n}`. There exists admissible advice `Γ` for which the profile
constructed in Section B.3 satisfies `R_0 = 1`. -/
theorem lemma_B_9 (n : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 1224 / 1000)
    (τ : ℕ → ℕ) (hτ : ValidTau n τ) :
    ∃ Γ : Advice, Γ.IsAdmissible n τ ∧ Rsuf n γ τ Γ 0 = 1 := by sorry

end BetterKMedian.LMPGreedy
