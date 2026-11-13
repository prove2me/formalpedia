-- Prove2me | Theorems.Thm_AutoregLTF_claim_1
-- name    : AutoregLTF.claim_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:54:59.571203+00:00
-- url     : https://prove2.me/theorems/f834550a-7f42-4b55-b77e-b3ac13dac3d1
-- title:
--   Claim 1, p.8 — the assignments (17)–(18) of $a^{(0)}$ are consistent
-- statement:
--   Let $m\ge2$ and $\theta\in\{0,\dots,2^m-1\}^m$. Consider the assignments (17a)–(17f) and (18), for all $j\in[m]$, of the auxiliary coefficients $a^{(0)}_\ell$. Then
--
--   1. every assigned index $\ell$ lies in $[p+1]=\{1,\dots,p+1\}$, and
--   2. if two assignments assign $a^{(0)}_\ell=q$ and $a^{(0)}_\ell=q'$ at the same index $\ell$, then $q=q'$.
--
--   So $a^{(0)}$ is well defined, and every index is set to at most one value even when (17e) or (17f) repeat an index.
--
--   Differences from the source:
--   - generalization: consistency for ℓ ∈ [p + 1] → every assigned index lies in [p + 1], and consistency at every index; reason: the paper presupposes the range (its a^{(0)} is a vector a_1, …, a_{p+1}, and the proof opens with "all defined indices lie in (0, p/6) ∪ (5p/6, p)"); with it the two forms of consistency coincide, so the Lean statement specializes to the claim
--   - encoding: "(17)–(18) assign a^{(0)}_ℓ = q" → (ℓ, q) is an entry of the list assign0 m θ; reason: the assignments are written as an explicit list, so that the claim is not true by construction
--   - encoding: θ ∈ {0, …, 2^m − 1}^m → θ : ℕ → ℤ with 0 ≤ θ j ≤ 2^m − 1 for j ∈ [m]; reason: only θ_1, …, θ_m are read and every vector in the range extends to such a function; same instances
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Claim 1 (proof of Lemma 2), p.8

import Mathlib
import Definitions.Def_AutoregLTF_coef

namespace AutoregLTF

/-- **Claim 1** (in the proof of Lemma 2), p.8 (PDF p.8).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"For any `ℓ ∈ [p + 1]`, if (17)–(18) assign both `a^{(0)}_ℓ = q` and `a^{(0)}_ℓ = q′`, then `q = q′`."

Stated on the list `assign0 m θ` of the assignments (17a)–(17f) and (18), `j = 1, …, m`: every
assigned index lies in `[p + 1]`, and two assignments with the same index assign the same value.

**Formalization Note.** Hypotheses are those of Lemma 2: `m ≥ 2` (p.4) and
`θ ∈ {0, …, 2^m − 1}^m`. The first conjunct (every index of (17)–(18) lies in `[p + 1]`) is presupposed
by the paper's "Define integer coefficients `a^{(0)}_1, …, a^{(0)}_{p+1}`" and is the first step of the
claim's proof ("all defined indices lie in `(0, p/6) ∪ (5p/6, p)`"); with it, consistency at every
index is the same as consistency at every `ℓ ∈ [p + 1]`. -/
theorem claim_1 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ∀ e ∈ assign0 m θ, (1 ≤ e.1 ∧ e.1 ≤ (p m : ℤ) + 1) ∧
      ∀ e' ∈ assign0 m θ, e'.1 = e.1 → e'.2 = e.2 := by sorry

end AutoregLTF
