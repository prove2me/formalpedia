-- Prove2me | Theorems.Thm_CliffordCert_Optimal_Supplement_rank_sensitive_upper_bound
-- name    : CliffordCert.Optimal.Supplement.rank_sensitive_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:40:18.731963+00:00
-- url     : https://prove2.me/theorems/7d2be78d-a229-4b5a-bf4f-763d3bbc7c17
-- title:
--   Theorem 5 — rank-sensitive certification upper bound
-- statement:
--   Let $d=2^n$, $r=2^q$ and $1\le q\le n$. For every density matrix $\sigma$ on $\mathbb C^d$ of complex rank $k\ge2$ and every $0<\varepsilon\le1$, put $K=2^{\lceil\log_2 k\rceil}$ and $R=\min\{r,K\}$. There exist an integer copy count $m$, a physical private-coin, quantum-only protocol and a finite list covering its encoder schedule such that the protocol distinguishes $\rho=\sigma$ from $\|\rho-\sigma\|_1\ge\varepsilon$ with success at least $2/3$ under each promise. Its resource bounds are
--
--   $$
--   \#\mathrm{settings}\le1+\frac{6K^2}{R^2},\qquad
--   m\le\left\lceil\frac{64\ln3}{\varepsilon^2}\right\rceil+
--   \frac{3096K^3}{R^2\varepsilon^2}.
--   $$
--
--   The same protocol satisfies the explicit uniform form of the displayed asymptotic bound:
--
--   $$
--   m\le\left(24768+32\ln3+\frac12\right)
--   \frac{k^3}{\min\{r,k\}^2\varepsilon^2}.
--   $$
--
--   The protocol and its fixed schedule may depend on the known reference and accuracy, but not on the unknown state. All alternatives are ambient density matrices, including leakage and coherences outside the support. Original-input encoders are arbitrary CPTP maps; Clifford compression is used after support reduction, so no original-input Clifford condition is imposed. This is the companion upper bound for each prescribed reference rank.
--
--   Differences from the source:
--   - encoding: at most 1+6K²/R² encoder settings → a list of CPTP maps covering every scheduled encoder, whose length obeys the same bound; reason: a family has at most that many distinct maps exactly when such a finite covering list exists
--   - encoding: K=2^ceil(log₂ k) and the exact real resource inequality (8) → Nat.clog 2 k defines K, natural copy and list counts are cast to reals, and only the leakage summand is rounded up; reason: the integer ceiling logarithm agrees for positive k and the displayed inequality is preserved without rounding the entire right side
--   - encoding: O(k³/(min{r,k}² ε²)) in Eq. (8) → the same witness obeys the uniform constant 24768+32 ln(3)+1/2; reason: §F.2 gives K<2k and R≥min{r,k}; k≥2 and ε≤1 absorb the leakage ceiling into this absolute constant
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 7 (PDF 8), Theorem 5, Eqs. (7)–(8); proof pp. 19–20 (PDF 20–21), §F.2; source.pdf SHA256 2199cc2ec4c0cc01bfa75380982fe283d38a544dcae40abe5a37198f1a088114

import Definitions.Def_CliffordCert_Optimal_Supplement_rank_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal.Supplement

/-- Cha–Lee, Theorem 5, p. 7 (PDF 8), Eqs. (7)–(8).
    The explicit final constant instantiates the O clause uniformly (F.2, pp. 19–20). -/
theorem rank_sensitive_upper_bound
    {n q k : ℕ} (hq : 1 ≤ q) (hqn : q ≤ n)
    (σ : Mat (Bits n)) (hσ : IsState σ) (hkr : σ.rank = k) (hk : 2 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (m : ℕ) (π : Protocol (Bits n) (Bits q) m)
      (settings : List (Mat (Bits n) →ₗ[ℂ] Mat (Bits q))),
      Certifies π σ ε ∧ CoversSchedule π settings ∧
      (settings.length : ℝ) ≤ 1 + 6 * (paddedDimension k : ℝ)^2 /
        (supportMessageDimension q k : ℝ)^2 ∧
      (m : ℝ) ≤ (leakageCopies ε : ℝ) +
        3096 * (paddedDimension k : ℝ)^3 / ((supportMessageDimension q k : ℝ)^2 * ε^2) ∧
      (m : ℝ) ≤ (24768 + 32 * Real.log 3 + 1 / 2) * rankRate q k ε := by sorry

end CliffordCert.Optimal.Supplement
