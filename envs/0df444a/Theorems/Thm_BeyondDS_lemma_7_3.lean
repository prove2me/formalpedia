-- Prove2me | Theorems.Thm_BeyondDS_lemma_7_3
-- name    : BeyondDS.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:04.588787+00:00
-- url     : https://prove2.me/theorems/9c24890b-ca19-4212-89de-1daf84be7311
-- title:
--   Lemma 7.3 — uniform sampler, simultaneously for every corrupt set $C$ with $|C|\le t$
-- statement:
--   Let $n=2t+1$ and $1\le K\le n$, give every identity an independent row of $K$ independent uniform destinations, and put $B=\min\{n,\lceil512n/K\rceil\}$. With probability at least $1-e^{-2n}$, every set $C\subseteq[n]$ with $|C|\le t$ has at most $B$ rows containing fewer than $K/16$ distinct destinations outside $C$.
--
--   The event quantifies over all $C$ at once: "The conclusion holds for every C simultaneously, so choosing C adaptively after observing trials does not invalidate it." This is what lets the first epoch tolerate an adaptive adversary.
--
--   Differences from the source:
--
--   - encoding: n and t → n = 2t + 1 throughout §7, with rows the uniform law on Fin n → Fin K → Fin n; reason: §7.1 fixes n = 2t + 1; same law
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 7.3, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_BeyondDS_TrialStep

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS

/-- Lemma 7.3 (Uniform sampler), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.23 (PDF 24): with `n = 2t + 1`, assign every identity an independent
row of `K` independent uniform destinations, `1 ≤ K ≤ n`, and let `B = min{n, ⌈512n/K⌉}`. With probability at least `1 − exp(−2n)`,
every set `C` with `|C| ≤ t` has at most `B` rows containing fewer than `K/16` distinct destinations outside `C`.

**Formalization Note.** `∀ C` is inside the event: "The conclusion holds for every C simultaneously, so choosing C adaptively after
observing trials does not invalidate it" (p.24). -/
theorem lemma_7_3 (t K : ℕ) (hK₁ : 1 ≤ K) (hKn : K ≤ 2 * t + 1) :
    ENNReal.ofReal (1 - Real.exp (-(2 * ((2 * t + 1 : ℕ) : ℝ)))) ≤
      (PMF.uniformOfFintype (Fin (2 * t + 1) → Fin K → Fin (2 * t + 1))).toOuterMeasure
        {rows | ∀ C : Finset (Fin (2 * t + 1)), C.card ≤ t →
          (Finset.univ.filter fun i => (distinctIn (rows i) Cᶜ : ℝ) < (K : ℝ) / 16).card ≤
            min (2 * t + 1) ⌈512 * ((2 * t + 1 : ℕ) : ℝ) / K⌉₊} := by sorry

end BeyondDS
