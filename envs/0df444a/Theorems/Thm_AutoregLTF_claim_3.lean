-- Prove2me | Theorems.Thm_AutoregLTF_claim_3
-- name    : AutoregLTF.claim_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:56:32.161343+00:00
-- url     : https://prove2.me/theorems/7c211f0b-66c1-4252-893e-d3269e408736
-- title:
--   Claim 3, p.11 — off the positions $\Pi$, every score is negative: $\sigma_r<0$
-- statement:
--   Let $m\ge2$, $\theta\in\{0,\dots,2^m-1\}^m$, $i\in[m]$ and $t\ge0$, and let $\sigma_r$ be the scores (24) with $B=2^{m+5}(m+2)$ and the coefficients $a$ of (17)–(18), (22)–(23). Then
--
--   $$\sigma_r<0\qquad\text{for every } 0\le r<p \text{ with } r\notin\Pi.$$
--
--   Together with Claim 2, the rule (16) writes a $0$ at every position of the next block that (15) leaves empty.
--
--   Differences from the source:
--   - encoding: the coefficients a defined by (17)–(18), (22)–(23) → aCoef m θ, a lookup in the explicit lists; reason: by Claim 1 and the disjointness of (22)–(23) the lookup is the paper's a
--   - encoding: θ ∈ {0, …, 2^m − 1}^m → θ : ℕ → ℤ with 0 ≤ θ j ≤ 2^m − 1 for j ∈ [m]; reason: only θ_1, …, θ_m are read and every vector in the range extends to such a function; same instances
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Claim 3 (proof of Lemma 2), p.11

import Mathlib
import Definitions.Def_AutoregLTF_sigma

namespace AutoregLTF

/-- **Claim 3** (in the proof of Lemma 2), p.11 (PDF p.11).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"`σ_r < 0` for every `0 ≤ r < p` with `r ∉ Π`", with `σ_r` of (24) for `B = 2^{m+5}(m + 2)` and the
coefficients `a` of (17)–(18), (22)–(23).

**Formalization Note.** Hypotheses are those of Lemma 2 and of p.9: `m ≥ 2` (p.4),
`θ ∈ {0, …, 2^m − 1}^m`, `i ∈ [m]`, `t ≥ 0`. -/
theorem claim_3 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t r : ℕ) (hr : r < p m) (hnot : ¬ InPi m r) :
    sigma m θ i t r < 0 := by sorry

end AutoregLTF
