-- Prove2me | Theorems.Thm_DSICHardRev_Supplement_theorem_1_2
-- name    : DSICHardRev.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:10:44.883555+00:00
-- url     : https://prove2.me/theorems/dffc7b9d-f490-4f6a-846b-93d059b67475
-- title:
--   Theorem 1.2 — $\mathrm{DSIC}_{\mathrm{XOS}}(m,\gamma)=\Omega((m/\gamma)^{1/5})$ for $\gamma\in[\log m,m]$
-- statement:
--   Let $\mathrm{DSIC}_{\mathrm{XOS}}(m,\gamma)$ be the best approximation ratio attainable on $m$ items with $2^\gamma$ bits of communication by a deterministic, individually rational (IR), no-negative-transfers (NNT), dominant-strategy incentive compatible (DSIC) mechanism for XOS valuations with values in the range $R$ of p.8.
--
--   **Theorem.** There is a constant $c>0$ such that for every $m\ge2$ and every real $\gamma$ with $\log_2 m\le\gamma\le m$ there is a number of bidders $n\ge1$ for which every deterministic mechanism for $n$ bidders on $m$ items that is IR, NNT and DSIC on $\mathcal D_{\mathrm{XOS}}(m)$, uses at most $2^\gamma$ bits and attains an $\eta$-approximation on $\mathcal D_{\mathrm{XOS}}(m)$ satisfies
--   $$
--   \eta\;\ge\;c\left(\frac{m}{\gamma}\right)^{1/5}.
--   $$
--
--   This is the XOS companion of the mission's goal (Theorem 1.1, exponent $1/7$ for gross substitutes): for the larger class of XOS valuations the hardness exponent improves to $1/5$.
--
--   **Formalization Note** The statement has exactly the shape of the published goal `DSICHardRev.theorem_1_1`, with the domain $\mathcal D_{\mathrm{XOS}}(m)$ in place of $\mathcal D_{\mathrm{GS}}(m)$ and exponent $1/5$. DSIC is required against all strategy profiles; communication is the worst case over the protocol tree; the approximation is written $\mathrm{OPT}\le\eta\cdot\text{welfare}$.
--
--   Differences from the source:
--
--   - reading: DSIC_XOS(m, γ) = Ω((m/γ)^{1/5}) for γ ∈ [log m, m], with the number of bidders unspecified → ∃ c > 0, ∀ m ≥ 2, ∀ real γ ∈ [log₂ m, m], ∃ n ≥ 1, every IR, NNT, DSIC mechanism on DXOS m with comm ≤ 2^γ and an η-approximation has c·(m/γ)^{1/5} ≤ η; reason: the base mission's published reading of the Ω and of DSIC_GS(m, γ) (the optimal ratio over all instances, which may use many bidders); the hard instances use many bidders (p.3)
--   - encoding: XOS valuations 2^M → ℝ+ → monotone XOS valuations on Fin m with every value in Rset m; reason: the paper's global conventions: valuations are monotone (p.9) and take values in R (p.8)
--   - encoding: E[welfare] ≥ (1/η)·OPT → welfare v T ≤ η · welfare of the mechanism's allocation for every disjoint T; reason: deterministic mechanism; the published IsApprox, no division by η
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Theorem 1.2, p.3 (DSIC_XOS(m, γ) defined in §1.2, p.3; proof: Proposition 3.3 p.13, Theorems 3.7 and 4.5, §4.5 p.24)

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_Supplement_Domains

namespace DSICHardRev

namespace Supplement

/-- **Theorem 1.2** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.3):
`DSIC_XOS(m, γ) = Ω((m/γ)^{1/5})` for `γ ∈ [log m, m]`, where `DSIC_XOS(m, γ)` is the optimal
approximation ratio attainable on `m` items with `2^γ` communication by a deterministic, IR, NNT,
DSIC mechanism for XOS valuations.

**Formalization Note.** Same shape as the published `DSICHardRev.theorem_1_1`. `Ω` is read as:
there is a constant `c > 0` such that for every `m ≥ 2` and every real `γ` with
`log₂ m ≤ γ ≤ m` there is a number of bidders `n` for which every deterministic mechanism
(`Mechanism`) for `n` bidders on the items `Fin m` that is IR, NNT and DSIC (against all strategy
profiles) on the domain `DXOS m` (monotone XOS valuations with values in the range `R` of p.8),
uses at most `2^γ` bits (worst case over the whole protocol tree) and attains an `η`-approximation
on `DXOS m` (`OPT ≤ η · welfare` on every profile) has `η ≥ c (m/γ)^{1/5}`. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, Real.logb 2 m ≤ γ → γ ≤ m →
      ∃ n : ℕ, 0 < n ∧ ∀ (M : Mechanism (Fin n) (Fin m)) (η : ℝ),
        M.IsIR (DXOS m) → M.IsNNT (DXOS m) → M.IsDSIC (DXOS m) →
        (M.comm : ℝ) ≤ (2 : ℝ) ^ γ → M.IsApprox (DXOS m) η →
        c * ((m : ℝ) / γ) ^ ((1 : ℝ) / 5) ≤ η := by sorry

end Supplement

end DSICHardRev
