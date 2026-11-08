-- Prove2me | Theorems.Thm_DPVerify_clip_mass_le
-- name    : DPVerify.clip_mass_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:29.187194+00:00
-- url     : https://prove2.me/theorems/b86846a6-a085-499d-8450-1a0d17e10c24
-- title:
--   Proof of Theorem 4.1, pp.15–16 — clipping $\tilde p_S=\min\{e^\varepsilon p_{S'},\max(e^{-\varepsilon}p_{S'},p_S)\}$ moves at most $2\delta$ mass
-- statement:
--   Let $\mathcal M$ be a finite set, $\varepsilon\ge0$, and let $p,p':\mathcal M\to[0,\infty)$ satisfy, for every $E\subseteq\mathcal M$,
--
--   $$
--   p(E)\le e^{\varepsilon}p'(E)+\delta\qquad\text{and}\qquad p'(E)\le e^{\varepsilon}p(E)+\delta .
--   $$
--
--   Let $\tilde p(m)=\min\{e^{\varepsilon}p'(m),\max(e^{-\varepsilon}p'(m),p(m))\}$. Then
--
--   $$
--   \sum_{m\in\mathcal M}|p(m)-\tilde p(m)|\;\le\;2\delta .
--   $$
--
--   In the approximate-DP part of the privacy proof of Theorem 4.1, $p=p_S$ and $p'=p_{S'}$ are the message laws of an $(\varepsilon,\delta)$-DP protocol on neighbouring samples; clipping $p_S$ into the multiplicative window around $p_{S'}$ costs at most $2\delta$ in total variation.
--
--   Differences from the source:
--   - generalization: the message laws $p_S$, $p_{S'}$ of an $(\varepsilon,\delta)$-DP protocol on neighbouring samples → any nonnegative masses on a finite set satisfying the two $(\varepsilon,\delta)$ inequalities on every subset; reason: the message laws are such masses
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.15 (PDF p.18) and p.16 (PDF p.19)

import Mathlib

set_option autoImplicit false

namespace DPVerify

/-- §4, proof of Theorem 4.1, the clipping display (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), pp.15–16 = PDF pp.18–19): for neighbouring
samples with message probabilities `p = p_S` and `p′ = p_{S′}`, the clipped
`p̃(m) = min{e^ε p′(m), max(e^{−ε} p′(m), p(m))}` satisfies `∑_m |p(m) − p̃(m)| ≤ 2δ` "by definition
of `(ε, δ)`-DP".

**Formalization Note** Stated for any nonnegative masses `p, p′` on a finite set `M` that satisfy
the two `(ε, δ)`-DP inequalities `p(E) ≤ e^ε p′(E) + δ` and `p′(E) ≤ e^ε p(E) + δ` for every
`E ⊆ M`; the message laws of an `(ε, δ)`-DP protocol on neighbouring samples are such masses. -/
theorem clip_mass_le {M : Type} [Fintype M] (p p' : M → ℝ) (hp : ∀ m, 0 ≤ p m)
    (hp' : ∀ m, 0 ≤ p' m) (ε δ : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ E : Finset M, ∑ m ∈ E, p m ≤ Real.exp ε * ∑ m ∈ E, p' m + δ)
    (h2 : ∀ E : Finset M, ∑ m ∈ E, p' m ≤ Real.exp ε * ∑ m ∈ E, p m + δ) :
    ∑ m, |p m - min (Real.exp ε * p' m) (max (Real.exp (-ε) * p' m) (p m))| ≤ 2 * δ := by sorry

end DPVerify
