-- Prove2me | Theorems.Thm_CritWinSpin_lemma_4_1
-- name    : CritWinSpin.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:37.499497+00:00
-- url     : https://prove2.me/theorems/528b716e-3a84-4aab-861e-ad1de2c40e97
-- title:
--   Lemma 4.1, p.13 — Hubbard–Stratonovich representation of $\pi^\rho_{J,h}$
-- statement:
--   Let $J\in\mathbb R^{N\times N}$ be positive semidefinite with $J=LL^\top$, and let $V$, $P(x\mid z)$ be as in (19). If $Z$ has density $q^*(z)\propto\exp(-V(z))$ and $X\sim P(\cdot\mid Z)$, then $X$ has law $\pi^\rho_{J,h}$, that is, for every $x\in A^N$,
--   $$\frac{\int P(x\mid z)e^{-V(z)}\,dz}{\int e^{-V(z)}\,dz}=\pi^\rho_{J,h}(x).$$
--
--   This reduces discrete sampling to sampling a continuous vector.
--
--   Differences from the source:
--   - encoding: X has marginal law π → the integral ratio at every x, with integrability of both integrands stated as conclusions; reason: the definition of the marginal; integrability rules out the junk value of the Bochner integral
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 4.1, p.13, eq. (19)

import Mathlib
import Definitions.Def_CritWinSpin_Wpot
open MeasureTheory
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 4.1, Hubbard–Stratonovich representation** (Liu–Zhang–Ren, STOC 2027 submission, manuscript
sha256 f77584da…, p.13). For `J = LLᵀ` positive semidefinite, if `Z` has density `∝ e^{−V}` and
`X ∼ P(· | Z)`, then `X` has law `π^ρ_{J,h}`. -/
theorem lemma_4_1 (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hJ : J.PosSemidef) (hL : J = L * L.transpose) (x : Config S (Fin N)) :
    Integrable (fun z : Fin N → ℝ => Real.exp (-hsV S L h z)) ∧
    Integrable (fun z : Fin N → ℝ => condP S L h z x * Real.exp (-hsV S L h z)) ∧
    (∫ z : Fin N → ℝ, condP S L h z x * Real.exp (-hsV S L h z)) /
        (∫ z : Fin N → ℝ, Real.exp (-hsV S L h z)) = gibbs S J h x := by sorry

end CritWinSpin
