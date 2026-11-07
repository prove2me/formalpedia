-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_4_2
-- name    : ArbSlowFP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:53.537007+00:00
-- url     : https://prove2.me/theorems/3e2f4695-2e7f-43e8-bb0e-12add5ba3a72
-- title:
--   Lemma 4.2 — remaining height gain across a parent bundle, with the same constant $A_k$
-- statement:
--   Let an order-$k$ clock have constant $A_k$ in condition (III). For every rational $\epsilon>0$ there is a threshold above which, for every bundle $W_k(a)W_k(a+1)\cdots W_k(a+L-1)$ with $L\ge1$ and starting index $a$ above the threshold, and at every prefix of it,
--   $$\chi(a+L)-H_{\mathrm{prefix}}\le\epsilon|W^{\mathrm{rem}}_{\mathrm{bundle}}|+A_k ,$$
--   where $|W^{\mathrm{rem}}_{\mathrm{bundle}}|$ is the number of plays remaining in the whole bundle. The threshold is a computable function of $\epsilon$.
--
--   The additive constant is charged once per bundle rather than once per phase, which is what lets reset actions wait through a long bundle.
--
--   **Formalization Note** $\epsilon=(e+1)/(n+1)$ ranges over all positive rationals. The clause that the threshold is computable reflects p.25: "All thresholds below are obtainable by finite calculations", "subsequent statements use the shorter phrase 'there is a threshold'".
--
--   Differences from the source:
--   - reading: "there is a threshold" → a computable rule Qbun on ϵ; reason: p.25 says all thresholds below are computable and that later statements abbreviate this; the proof of Proposition 7.8 composes the rule into Q̂_{k+1}
--   - encoding: rational ϵ > 0 → (e+1)/(n+1); reason: this reaches every positive rational; Mathlib has no Primcodable ℚ
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.26, Lemma 4.2

import Mathlib
import Definitions.Def_ArbSlowFP_IsClock

open Matrix

namespace ArbSlowFP

/-- Lemma 4.2, p.26 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): for every
rational `ϵ > 0` there is a threshold above which the remaining-height bound (16) holds with the same
constant `A_k` across every bundle `W_k(a) ⋯ W_k(a+L-1)`, `L ≥ 1`. Here `H_end = χ(a+L)` and the
remaining length counts the rest of the whole bundle.

**Formalization Note.** `ϵ = (e+1)/(n+1)`. The rule `Qbun` is computable because p.25 says "All
thresholds below are obtainable by finite calculations" and "subsequent statements use the shorter
phrase 'there is a threshold'", and the proof of Proposition 7.8 composes it into `Q̂_{k+1}`. -/
theorem lemma_4_2 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) :
    ∃ Qbun : ℕ → ℕ → ℕ, Computable₂ Qbun ∧
      ∀ e n a, Qbun e n ≤ a → ∀ L, 1 ≤ L → ∀ h, h ≤ (bundle d.W a L).length →
        d.chiAt (a + L) - height (scoreAfter d.A (d.r a) ((bundle d.W a L).take h))
          ≤ ((e : ℚ) + 1) / ((n : ℚ) + 1) * (((bundle d.W a L).length : ℚ) - (h : ℚ)) + d.Ak := by sorry

end ArbSlowFP
