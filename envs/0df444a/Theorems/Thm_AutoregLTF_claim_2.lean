-- Prove2me | Theorems.Thm_AutoregLTF_claim_2
-- name    : AutoregLTF.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:57.763064+00:00
-- url     : https://prove2.me/theorems/8a67fc58-6c46-41db-a825-7faee0edb45a
-- title:
--   Claim 2, p.9 — on the positions $\Pi$, the scores (24) reproduce the next block: $\widehat E_r=\mathbf 1\{\sigma_r\ge0\}$
-- statement:
--   Let $m\ge2$, $\theta\in\{0,\dots,2^m-1\}^m$, $i\in[m]$ and $t\ge0$. Let $B=2^{m+5}(m+2)$ and let $a$ be the coefficients of (17)–(18), (22)–(23). With $\widehat E=(0,E^t_{\theta,i},E^{t+1}_{\theta,i})$ and the scores
--
--   $$\sigma_r=-B+\sum_{\ell=1}^{p+1}a_\ell\,\widehat E_{r-\ell}\qquad(0\le r<p),$$
--
--   we have
--
--   $$\widehat E_r=\mathbf 1\{\sigma_r\ge0\}\qquad\text{for every } r\in\Pi.$$
--
--   At the positions where the block (15) stores information, the threshold rule (16) applied to the true history outputs the true next bit.
--
--   Differences from the source:
--   - encoding: the coefficients a defined by (17)–(18), (22)–(23) → aCoef m θ, a lookup in the explicit lists; reason: by Claim 1 and the disjointness of (22)–(23) the lookup is the paper's a
--   - encoding: Ê indexed by −p − 1, …, p − 1 → Ehat m θ i t : ℤ → Bool, false outside that range; reason: (24) reads only indices r − ℓ ∈ [−p − 1, p − 2]; same values
--   - encoding: θ ∈ {0, …, 2^m − 1}^m → θ : ℕ → ℤ with 0 ≤ θ j ≤ 2^m − 1 for j ∈ [m]; reason: only θ_1, …, θ_m are read and every vector in the range extends to such a function; same instances
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Claim 2 (proof of Lemma 2), p.9

import Mathlib
import Definitions.Def_AutoregLTF_sigma

namespace AutoregLTF

/-- **Claim 2** (in the proof of Lemma 2), p.9 (PDF p.9).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"`Ê_r = 1{σ_r ≥ 0}` for every `r ∈ Π`", where `Ê = (0, E^t_{θ,i}, E^{t+1}_{θ,i})` and
`σ_r = −B + ∑_{ℓ=1}^{p+1} a_ℓ Ê_{r−ℓ}` (24) with `B = 2^{m+5}(m + 2)` and the coefficients `a` of
(17)–(18), (22)–(23).

**Formalization Note.** Hypotheses are those of Lemma 2 and of p.9: `m ≥ 2` (p.4),
`θ ∈ {0, …, 2^m − 1}^m`, `i ∈ [m]`, `t ≥ 0`. `Π ⊆ {0, …, p − 1}`, so `Ê_r` is the bit
`E^{t+1}_{θ,i,r}` of the true next block. -/
theorem claim_2 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t r : ℕ) (hr : InPi m r) :
    Ehat m θ i t r = decide (0 ≤ sigma m θ i t r) := by sorry

end AutoregLTF
