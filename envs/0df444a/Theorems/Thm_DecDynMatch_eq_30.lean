-- Prove2me | Theorems.Thm_DecDynMatch_eq_30
-- name    : DecDynMatch.eq_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:01:15.06135+00:00
-- url     : https://prove2.me/theorems/4f857ea1-8094-4f82-8f25-c323b92aaa2b
-- title:
--   Eq. (30) — finite-prefix mismatch bound for every replay rule with (12)
-- statement:
--   Let $F$ be a replay rule with (12). For every dynamic matching instance $I$, including one whose final market is empty, and every horizon $T\ge 0$, the mismatch cost of SC-DA with replay rule $F$ satisfies
--   $$
--   D_F(T;I)\ \le\ \min\bigl\{\,T,\ \Psi_F^{\circ 3}(t^*+1)+U\,N_F(T)\,\bigr\}. \tag{30}
--   $$
--   The first term charges every round before calibration; each of the at most $N_F(T)$ maintenance windows meeting the first $T$ rounds costs at most $U$.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: M_t = m*_t → IsPOSM I t (M F I t); reason: strict rankings make the POSM unique, so the two agree
--   - encoding: N_F(T) = #{m ≥ 0 : F^{∘m}(H) < T} → count over m < T; reason: F^{∘m}(H) ≥ H + m > m for a rule with (12), so no index is lost
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. A.4, eq. (30), p.20

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_Psi
import Definitions.Def_DecDynMatch_NF
import Definitions.Def_DecDynMatch_D

namespace DecDynMatch

/-- **Finite-prefix accounting, eq. (30).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), App. A.4, p.20: "Charging at most one per round before calibration and using Lemma 7
gives D_F(T; I) ≤ min{T, Ψ_F^{∘3}(t* + 1) + U N_F(T)}. (30) This also covers prefixes ending before
calibration. If the final market is empty, D_F(T; I) ≤ min{T, t* − 1}, so the same bound holds; at
T = 0, both sides are zero."

For every replay rule `F` with (12), every instance (the final market may be empty) and every
horizon `T`. -/
theorem eq_30 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (T : ℕ) :
    D F I T ≤ min T ((Psi K F)^[3] (tstar I + 1) + U K * NF K F T) := by sorry

end DecDynMatch
