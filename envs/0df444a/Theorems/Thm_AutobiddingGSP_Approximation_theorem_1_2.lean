-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_theorem_1_2
-- name    : AutobiddingGSP.Approximation.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:28:52.573331+00:00
-- url     : https://prove2.me/theorems/2da3dd51-a598-4673-9b84-68949a801639
-- title:
--   Theorem 1.2 — approximate autobidding equilibria: PPAD membership at inverse-exponential precision and PPAD-hardness for every fixed 0 ≤ γ < 1 (ABE-B and ABE-R)
-- statement:
--   For GSP sponsored shopping auctions, for both ABE-B and ABE-R:
--
--   * **Membership.** Computing a γ-approximate autobidding equilibrium is in PPAD when $\gamma$ is inverse-exponential in the input size: (i) uniformly, for rational $0<\gamma<1$ given in binary with the auction; (ii) for every rational precision $\gamma(N)\in(0,1)$ of the instance length $N$ computable in polynomial time (in particular $\gamma(N)=2^{-p(N)}$ for every polynomial $p\ge1$).
--   * **Hardness.** For every fixed $0\le\gamma<1$, computing a γ-approximate autobidding equilibrium is PPAD-hard, with real answers (every equilibrium, including irrational exact ones at $\gamma=0$) and with rational answer codes — and, by the Remark, even when the number of slots equals the number of items and all click-through rates are one.
--
--   Differences from the source:
--   - generalization: γ inverse-exponential in the input size → (i) every rational 0 < γ < 1 given in the input, and (ii) every polynomial-time computable rational precision γ(N) ∈ (0,1); reason: both contain γ = 2^{−p(N)} for every polynomial p; (ii) is the paper's remark that the construction works for constant, inverse-polynomial and inverse-exponential γ
--   - generalization: computing a γ-approximate equilibrium (α, π) is PPAD-hard → hardness both with real answers that are the multiplier vector α of any equilibrium (decoded through exact comparisons) and with rational answer codes of (α, π); reason: a decoder from α also decodes (α, π); the real form keeps every real equilibrium at γ = 0
--   - encoding: PPAD; PPAD-hard → QuasiStrictNE.PPAD (total, reduces to End-of-Line); CEPolytopeHard.PPADHard; RealPPADHard; reason: published definitions and their real-answer extension
--   - encoding: the Remark's restricted instances (slots = items, CTRs one) → every clause for r = false (all instances) and r = true (restricted); reason: both statements of the source in one family
--   - encoding: the ROI cap A → A = A₀ = 1 + ∑v/min v of the instance (p. 8); reason: the paper's chosen cap
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Theorem 1.2 and the Remark after it, p. 3 (PDF 3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QuasiStrictNE_PPAD
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_AutobiddingGSP_Approximation_Search

namespace AutobiddingGSP.Approximation

/-- **Theorem 1.2** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 3 (PDF 3), with the Remark after it). For GSP sponsored shopping
auctions the following membership and hardness results hold for both ABE-B and ABE-R.

* **Membership.** Computing a γ-approximate autobidding equilibrium is in PPAD when `γ` is
  inverse-exponential in the input size: (i) for rational `0 < γ < 1` given in binary with the
  auction (so `γ ≥ 2^{−N}`, uniformly); and (ii) for every precision `γ(N) ∈ (0, 1)` of the
  length `N` of the instance that is rational and computable in polynomial time, in particular
  `γ(N) = 2^{−p(N)}` for every polynomial `p ≥ 1`.
* **Hardness.** For every fixed `0 ≤ γ < 1`, computing a γ-approximate autobidding equilibrium is
  PPAD-hard, with real answers (every equilibrium, including irrational exact ones at `γ = 0`) and
  with rational answer codes; by the Remark this holds even when the number of slots equals the
  number of items and all click-through rates are one (`r = true`).

Both clauses are stated for the general instances (`r = false`) and the restricted ones
(`r = true`). -/
theorem theorem_1_2 :
    (∀ (m : Model) (r : Bool), ABESearchUniform m r ∈ QuasiStrictNE.PPAD) ∧
    (∀ (m : Model) (r : Bool) (prec : ℕ → ℚ),
      CookPvsNP.PolyTimeComputable
          (fun s : List Bool => QAlgorithms.LocalHamiltonian.encRat (prec s.length)) →
        (∀ N, 0 < prec N ∧ prec N < 1) →
        ABESearch m (fun N => (prec N : ℝ)) r ∈ QuasiStrictNE.PPAD) ∧
    (∀ (m : Model) (r : Bool) (γ : ℝ), 0 ≤ γ → γ < 1 →
      RealPPADHard (ABERealSearch m γ r) ∧
        CEPolytopeHard.PPADHard (ABESearch m (fun _ => γ) r)) := by sorry

end AutobiddingGSP.Approximation
