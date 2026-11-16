-- Prove2me | Theorems.Thm_CliffordCert_Optimal_Supplement_uniform_support_lower_bound
-- name    : CliffordCert.Optimal.Supplement.uniform_support_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:41:02.09113+00:00
-- url     : https://prove2.me/theorems/7fdbf0b5-0751-4e16-9726-8ced6d6a0a18
-- title:
--   Theorem 6 — lower bound for a uniform state on a support
-- statement:
--   There exist absolute constants $c>0$ and $\varepsilon_*>0$, independent of every dimension, rank, projection, separation and protocol, with the following property. For every $d=2^n$, $r=2^q$ with $1\le q\le n$, every integer $2\le k\le d$, every rank-exactly-$k$ orthogonal projection $P$ on $\mathbb C^d$ and every $0<\varepsilon\le\varepsilon_*$, any private-coin, quantum-only protocol certifying the known reference $\sigma=P/k$ with success at least $2/3$ under each promise must use
--
--   $$
--   m\ge c\,\frac{k^3}{\min\{r,k\}^2\varepsilon^2}.
--   $$
--
--   The encoders are arbitrary CPTP maps with a schedule fixed before the unknown state, and the referee can use any collective binary measurement. Certification tests against every ambient alternative state at full trace-norm distance at least $\varepsilon$. No support constraint on alternatives or Clifford constraint on encoders is assumed. This supplies the companion lower bound for every support of each prescribed rank, including non-power-of-two ranks and ranks two through seven.
--
--   Differences from the source:
--   - encoding: rank-k orthogonal projection and known state P/k → a Hermitian idempotent of complex matrix rank k and the computed matrix (k:ℂ)⁻¹ • P; reason: these are the same projections and references, and k≥2 excludes division by zero
--   - encoding: certification in the model of Eq. (15) → every published-model Protocol satisfying the fixed-reference Certifies predicate; reason: this includes all independent private coins through their averaged local CPTP maps and retains success under both promises
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), pp. 7–8 (PDF 8–9), Theorem 6, Eq. (9); proof pp. 20–22 (PDF 21–23), §F.3; source.pdf SHA256 2199cc2ec4c0cc01bfa75380982fe283d38a544dcae40abe5a37198f1a088114

import Definitions.Def_CliffordCert_Optimal_Supplement_rank_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal.Supplement

/-- Cha–Lee, Theorem 6, pp. 7–8 (PDF 8–9), Eq. (9).
    Both absolute constants precede every instance parameter. -/
theorem uniform_support_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ εstar : ℝ, 0 < εstar ∧
    ∀ (n q k : ℕ), 1 ≤ q → q ≤ n → 2 ≤ k → k ≤ 2^n →
    ∀ P : Mat (Bits n), IsOrthogonalProjection P → P.rank = k →
    ∀ ε : ℝ, 0 < ε → ε ≤ εstar →
    ∀ (m : ℕ) (π : Protocol (Bits n) (Bits q) m),
      Certifies π (uniformSupport P k) ε → c * rankRate q k ε ≤ (m : ℝ) := by sorry

end CliffordCert.Optimal.Supplement
