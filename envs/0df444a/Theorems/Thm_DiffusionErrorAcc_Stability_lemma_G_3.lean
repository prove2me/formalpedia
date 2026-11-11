-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_G_3
-- name    : DiffusionErrorAcc.Stability.lemma_G_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:57:43.540755+00:00
-- url     : https://prove2.me/theorems/c20e304b-519e-47ae-aa44-2a6429428095
-- title:
--   Lemma G.3 — E_ν f − E_µ f ≤ E_µ[f log(ν/µ)] + KL(µ‖ν) for f with values in [0, 1]
-- statement:
--   Let $\mu,\nu$ be probability distributions on a measurable space $X$ with everywhere positive densities $p_\mu,p_\nu$ with respect to a common reference measure $\lambda$, write $\nu/\mu$ for the ratio $p_\nu/p_\mu$, and let $f:X\to[0,1]$ be measurable. Then
--   $$\mathbb E_\nu[f]-\mathbb E_\mu[f]\le\mathbb E_\mu\big[f\log(\nu/\mu)\big]+\mathrm{KL}(\mu\|\nu).$$
--   The inequality is a one-sided variational bound comparing two laws through a single bounded statistic; in the paper it is applied to the path laws of two SDEs to start the adjoint argument of Lemma A.1.
--
--   **Formalization Note.** $\mathrm{KL}$ is Mathlib's `klDiv` of the two laws `lam.withDensity`; the statement assumes $\mathrm{KL}(\mu\|\nu)<\infty$ and reads it as a real number.
--
--   Differences from the source:
--   - encoding: µ, ν distributions on a set X with positive density → densities pμ, pν > 0, measurable, integrable with integral 1 with respect to an arbitrary measure lam on a measurable space X; µ = lam.withDensity pμ, ν = lam.withDensity pν; reason: the reference measure of the densities is left unnamed in the source
--   - encoding: KL(µ‖ν) ∈ [0, ∞] → hypothesis klDiv µ ν ≠ ∞ and KL read as a real number; reason: if KL(µ‖ν) = ∞ the right side is +∞ or the undefined −∞ + ∞; only that case is excluded
--   - encoding: f : X → [0, 1] a function → f measurable with values in [0, 1]; reason: §2.3: all functions are assumed measurable
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 37, Lemma G.3

import Mathlib

open MeasureTheory InformationTheory
open scoped ENNReal

namespace DiffusionErrorAcc.Stability

/-- Lemma G.3 (p. 37). Let `µ, ν` be distributions on a set `X` with positive densities `pμ, pν`
(with respect to a common reference measure `λ`), and `f : X → [0, 1]`. Then
`E_ν[f] − E_µ[f] ≤ E_µ[f log(ν/µ)] + KL(µ‖ν)`, where `ν/µ` is the ratio of densities.
Stated when `KL(µ‖ν) < ∞` (otherwise the right side may be `−∞ + ∞`). -/
theorem lemma_G_3 {X : Type*} [MeasurableSpace X] (lam : Measure X)
    (pμ pν : X → ℝ) (hpμm : Measurable pμ) (hpνm : Measurable pν)
    (hpμ : ∀ x, 0 < pμ x) (hpν : ∀ x, 0 < pν x)
    (hpμ1 : ∫ x, pμ x ∂lam = 1) (hpν1 : ∫ x, pν x ∂lam = 1)
    (hpμi : Integrable pμ lam) (hpνi : Integrable pν lam)
    (f : X → ℝ) (hfm : Measurable f) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hKL : klDiv (lam.withDensity fun x => ENNReal.ofReal (pμ x))
      (lam.withDensity fun x => ENNReal.ofReal (pν x)) ≠ ∞) :
    (∫ x, f x ∂(lam.withDensity fun x => ENNReal.ofReal (pν x))) -
        ∫ x, f x ∂(lam.withDensity fun x => ENNReal.ofReal (pμ x)) ≤
      (∫ x, f x * Real.log (pν x / pμ x) ∂(lam.withDensity fun x => ENNReal.ofReal (pμ x))) +
        (klDiv (lam.withDensity fun x => ENNReal.ofReal (pμ x))
          (lam.withDensity fun x => ENNReal.ofReal (pν x))).toReal := by sorry

end DiffusionErrorAcc.Stability
