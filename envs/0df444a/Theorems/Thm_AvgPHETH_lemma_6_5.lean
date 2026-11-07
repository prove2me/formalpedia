-- Prove2me | Theorems.Thm_AvgPHETH_lemma_6_5
-- name    : AvgPHETH.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:30.445756+00:00
-- url     : https://prove2.me/theorems/1a1be5a7-5fb0-46d3-bcb7-15c6a46a1e5c
-- title:
--   Lemma 6.5 — $\mathrm S_2^k\mathrm{TIME}^O[t]\subseteq\mathrm{DTIME}^{\Sigma_k^{p,O}}[\mathrm{poly}(t)]$
-- statement:
--   Suppose $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$ for an oracle $O$ and a fixed $d\ge2$. For every $0\le k<d$ and every time-constructible bound $t(n)\ge n$,
--
--   $$\mathrm S_2^k\mathrm{TIME}^O[t(n)]\subseteq\mathrm{DTIME}^{\Sigma_k^{p,O}}[\mathrm{poly}(t(n))].$$
--
--   This converts symmetric alternations into oracle queries.
--
--   Differences from the source:
--   - encoding: $\mathrm{poly}(t(n))$ → $t(n)^e+e$, with $e$ depending on $L$; reason: every polynomial in $t$ is bounded by one of this form, since $t(n)\ge n$
--   - encoding: $\Sigma_d^{p,O}$ on the usual machine → the two-tape machine KarpLiptonOM.OracleTM; reason: same classes up to polynomial overhead
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 6.5, p.29 (PDF 31)

import Mathlib
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_S2kTIME
import Definitions.Def_AvgPHETH_DTimeOracle
import Definitions.Def_AvgPHETH_IsTimeConstructible

namespace AvgPHETH

/-- **Lemma 6.5** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.29 (PDF 31)). Suppose `Σ_d^{p,O} × {U, T} ⊆ AvgP^O` for an oracle `O` and a fixed `d ≥ 2`. For every `0 ≤ k < d` and
time-constructible bound `t(n) ≥ n`, `S₂^kTIME^O[t(n)] ⊆ DTIME^{Σ_k^{p,O}}[poly(t(n))]`.

**Formalization Note** `poly(t)` is `t^e + e`, with `e` depending on `L`. -/
theorem lemma_6_5 (O : Set (List Bool)) (d k : ℕ) (t : ℕ → ℕ) (hd : 2 ≤ d)
    (hAvg : TimesUT O (SigmaPO O d)) (hk : k < d) (ht : IsTimeConstructible t)
    (L : Set (List Bool)) (hL : S2kTIME O k t L) :
    ∃ e : ℕ, DTimeOracle (SigmaPO O k) (fun n => t n ^ e + e) L := by sorry

end AvgPHETH
