-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_lemma_B_8
-- name    : BetterKMedian.LMPGreedy.lemma_B_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:20:04.68048+00:00
-- url     : https://prove2.me/theorems/1eb59522-0604-4c29-b6e0-95f4109ed372
-- title:
--   Lemma B.8 — correct admissible advice yields a feasible dual solution of value $2-(\gamma-1)^2$
-- statement:
--   Fix $n\ge2$, $\gamma\in(1,1.224]$ and first bidding times $\tau_j\in\{j,\dots,n\}$. For every admissible advice $\Gamma$ (Definition B.6 and Property B.7) whose constructed profile satisfies $R_0=1$, the variables $(\hat g,g,s,t)$ produced by the procedure of Section B.3 (Algorithm 2, Table 2, (26)) are a feasible solution of value $\rho=2-(\gamma-1)^2$ of the inner program of Definition 3.7 for $\tau$.
--
--   Differences from the source:
--   - encoding: first bidding times τ_j ∈ {j, …, n} for every client j → `τ : ℕ → ℕ` with `ValidTau n τ` (j ≤ τ j ≤ n for 1 ≤ j ≤ n); values at other indices unused; reason: same choices of τ
--   - encoding: advice Γ = (T⋆, {µ⋆_j}_{τ_j = T⋆}, ĝ⋆_n when T⋆ = n) (Definition B.6) → `Γ : Advice` with fields `T`, `mu : ℕ → ℝ`, `gn : ℝ`; entries the construction does not use are ignored; `Advice.IsAdmissible n τ Γ` is Definition B.6 with Property B.7; reason: same advice
--   - encoding: the procedure of Section B.3 (memberships (23), Algorithm 2 with (24), (25), Table 2 and (26)) → `ghat`, `gCert`, `sCert`, `tCert`, `Rsuf` of `Def_BetterKMedian_LMPGreedy_DualCertificate`, functions of (n, γ, τ, Γ); "returns ⊥ unless R_0 = 1" is the hypothesis `Rsuf n γ τ Γ 0 = 1`; reason: same construction; Lean division by 0 is 0 but every denominator is positive in this parameter range (proof of Lemma B.11)
--   - encoding: variables d_j, f, r_{j,k} for 1 ≤ j ≤ k ≤ n + 1 (Definition 3.2) → functions `d : ℕ → ℝ`, `r : ℕ → ℕ → ℝ` and `f : ℝ`, constraints only on the paper's 1-based ranges; values outside them occur in no constraint and not in the objective; reason: same feasible points restricted to the index ranges
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Lemma B.8, printed p. 42 (PDF 44)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_FRPrimalDual
import Definitions.Def_BetterKMedian_LMPGreedy_DualCertificate

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Lemma B.8** (Buhai et al. 2026, printed p. 42, PDF 44). Fix `n ≥ 2`, `γ ∈ (1, 1.224]` and
first bidding times `τ_j ∈ {j, …, n}`. For every admissible advice `Γ` whose constructed profile
satisfies `R_0 = 1`, the procedure of Section B.3 (Algorithm 2, Table 2, (26)) produces a
feasible solution of value `2 − (γ − 1)²` to the inner program of Definition 3.7 for `τ`. -/
theorem lemma_B_8 (n : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 1224 / 1000)
    (τ : ℕ → ℕ) (hτ : ValidTau n τ) (Γ : Advice) (hΓ : Γ.IsAdmissible n τ)
    (hR : Rsuf n γ τ Γ 0 = 1) :
    DualFeasible n γ τ (ghat n γ τ Γ) (gCert n γ τ Γ) (sCert n γ τ Γ) (tCert n γ τ Γ)
      (2 - (γ - 1) ^ 2) := by sorry

end BetterKMedian.LMPGreedy
