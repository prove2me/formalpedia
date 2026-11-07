-- Prove2me | Theorems.Thm_AvgPHETH_proposition_4_10
-- name    : AvgPHETH.proposition_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:32:01.319305+00:00
-- url     : https://prove2.me/theorems/91a0165e-f2ce-46d9-b819-d63e65f66440
-- title:
--   Proposition 4.10 — composition of logarithmic savings
-- statement:
--   For any integers $k,k'\ge0$,
--
--   $$m\in\mathcal L_{\downarrow k}(n),\quad \ell\in\mathcal L_{\downarrow k'}(m(n))\implies \ell\in\mathcal L_{\downarrow(k+k')}(n).$$
--
--   This lets the savings of successive compression steps be added.
--
--   Differences from the source:
--   - encoding: $\Theta(\cdot)$ and "for any length function $m$ with $m(n)\ge2$ for sufficiently large $n$" → explicit constants $a,A$ and threshold, with the assumption on $m$ a clause of the class; reason: same class for every admissible $m$
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Proposition 4.10, p.19 (PDF 21)

import Mathlib
import Definitions.Def_AvgPHETH_LDown

namespace AvgPHETH

/-- **Proposition 4.10** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.19 (PDF 21)). For any integers `k, k' ≥ 0`, `m ∈ 𝓛_{↓k}(n)` and
`ℓ ∈ 𝓛_{↓k'}(m(n))` imply `ℓ ∈ 𝓛_{↓(k+k')}(n)`. -/
theorem proposition_4_10 (k k' : ℕ) (m ℓ : ℕ → ℕ) (hm : m ∈ LDown k id) (hℓ : ℓ ∈ LDown k' m) :
    ℓ ∈ LDown (k + k') id := by sorry

end AvgPHETH
