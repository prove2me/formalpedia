-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_iterated_entropy_price
-- name    : BauerleRiederMDP.Indifference.iterated_entropy_price
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:00.197129+00:00
-- url     : https://prove2.me/theorems/9dc16bc1-4a9e-4dab-8976-55a604a765c9
-- title:
--   §4.9, p.140 — the price by iterating the expectation operator of $\mathbb Q$
-- statement:
--   For a claim $H\ge 0$ with maturity $N$, $n<N$ and $s,\hat s>0$, the indifference price is obtained from the price one period later by one step under the minimal entropy martingale measure:
--   $$
--   v_n(H,s,\hat s)=\frac1\gamma\,\mathbb E_{\mathbb Q}\Bigl[\log\mathbb E_{\mathbb Q}\bigl[e^{\gamma v_{n+1}(H,\,s\tilde R,\,\hat s\hat R)}\mid S_1\bigr]\Bigr],
--   $$
--   where $S_1=s\tilde R$. Iterating this from $n=N-1$ down to $n=0$ computes the price.
--
--   This is the multiperiod form of the formula of Remark 4.9.3, obtained through the consistency condition of Theorem 4.9.4 c).
--
--   Differences from the source:
--   - reading: we can also compute the indifference price by iterating the expectation operator with respect to the minimal entropy martingale measure (a sentence without a display) → the one-step recursion displayed above; reason: this is what part c) and the formula of Remark 4.9.3 combine to, and it is the precise form of the sentence
--   - reading: (FM) prints only d̂ < û → hypothesis 0 ≤ d̂; reason: the multiperiod model puts the relative price changes in 𝒵 := ℝ₊ × ℝ₊ (p.138), so the prices stay in ℝ₊ where the claim is non-negative
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.140, paragraph after the proof of Theorem 4.9.4

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_IsIndifferencePrice
import Definitions.Def_BauerleRiederMDP_Indifference_Market_Q

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- The indifference price can be computed by iterating the expectation operator with respect to the
minimal entropy martingale measure (Bäuerle & Rieder, Markov Decision Processes with Applications
to Finance (2011), §4.9, p.140, PDF 154): by part c) of Theorem 4.9.4 and Remark 4.9.3,
`v_n(H, s, ŝ) = (1/γ) 𝔼_ℚ[log 𝔼_ℚ[e^{γ v_{n+1}(H, s R̃, ŝ R̂)} | S₁]]`.

**Formalization Note.** The book states this in words; the display above is what combining part c)
with the formula of Remark 4.9.3 gives, with `S₁ = s R̃` and `Ŝ₁ = ŝ R̂` as one period of the
market, the pair `(R̃_{n+1}, R̂_{n+1})` having the law of `(R̃, R̂)`. `0 ≤ d̂` is the book's
`𝒵 := ℝ₊ × ℝ₊` (p.138). -/
theorem iterated_entropy_price (M : Market) (hdhat : 0 ≤ M.dhat) (N : ℕ) (H : Claim) (n : ℕ)
    (hn : n < N) (s ŝ : ℝ) (hs : 0 < s) (hŝ : 0 < ŝ) :
    M.indifferencePrice N H n s ŝ = 1 / M.γ * ∫ ω, Real.log
      ((M.Q[fun ω' => Real.exp (M.γ *
          M.indifferencePrice N H (n + 1) (s * M.Rt ω') (ŝ * M.Rh ω')) |
        MeasurableSpace.comap (fun ω' => s * M.Rt ω') inferInstance]) ω) ∂M.Q := by sorry

end BauerleRiederMDP.Indifference
