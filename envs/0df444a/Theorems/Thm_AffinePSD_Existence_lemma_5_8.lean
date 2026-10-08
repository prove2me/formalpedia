-- Prove2me | Theorems.Thm_AffinePSD_Existence_lemma_5_8
-- name    : AffinePSD.Existence.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:38.641569+00:00
-- url     : https://prove2.me/theorems/12fe2322-1c38-4d00-9f5c-3a8242e791f0
-- title:
--   Lemma 5.8 — an S_d^+ ∪ {Δ}-valued càdlàg solution of the martingale problem for A from every x
-- statement:
--   Let $(\alpha,b,\beta^{ij},c=0,\gamma=0,m,\mu)$ be an admissible parameter set and $\mathcal A$ the operator (2.12). Then for every $x\in S_d^+$ there is a càdlàg process $X$ with values in the one-point compactification $S_d^+\cup\{\Delta\}$ and $X_0=x$ such that
--   $$f(X_t)-\int_0^t\mathcal Af(X_s)\,ds$$
--   is a martingale for every $f\in\mathcal S_+$, with the convention $f(\Delta)=\mathcal Af(\Delta)=0$. Moreover the integrands of (2.12) are integrable.
--
--   Proposition 5.9 shows that this solution is unique in law and affine, which gives the existence part of Theorem 2.4.
--
--   **Formalization Note** The probability space is existentially quantified. $S_d^+\cup\{\Delta\}$ carries its Borel $\sigma$-algebra, and $X$ is a solution in the sense of `SolvesMP` (natural filtration, $X_0=x$ almost surely, càdlàg paths in time $\mathbb R_{\ge0}$). $\mathcal S_+$ is represented by Schwartz functions on $M_d$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 5.8, p. 48

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Existence_Generator
import Definitions.Def_AffinePSD_Existence_MartingaleProblem

open MeasureTheory
open scoped NNReal SchwartzMap

namespace AffinePSD.Existence

/-- Lemma 5.8 (arXiv:0910.0137v3, §5.2, p. 48): under the standing assumptions of §5.2 (an
admissible parameter set with `c = 0`, `γ = 0`, p. 41), for every `x ∈ S_d^+` there is an
`S_d^+ ∪ {Δ}`-valued càdlàg solution `X` of the martingale problem for `A` of (2.12) with
`X_0 = x`: `f(X_t) − ∫_0^t A f(X_s) ds` is a martingale for every `f ∈ S_+`.
Formalization Note: the probability space is existentially quantified; `S_d^+ ∪ {Δ}` is the
one-point compactification with its Borel σ-algebra; `f(Δ) = A f(Δ) = 0`; `f ∈ S_+` ranges over
restrictions of Schwartz functions on `M_d`; the martingale property is with respect to the natural
filtration of `X` (`SolvesMP`), the test pairs being `(f, A f)` for `f ∈ S_+`, extended by `0`
at `Δ`; the conjunct `GeneratorIntegrable` (the integrands of (2.12) are integrable) guards against
Lean's junk value of a non-integrable Bochner integral; càdlàg is the platform predicate
`EthierKurtz.HasCadlagPaths` with time in `ℝ≥0`. -/
theorem lemma_5_8 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.Admissible χ P)
    (hc : P.c = 0) (hγ : P.γ = 0) (x : Cone d) :
    GeneratorIntegrable χ P ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pr : Measure Ω) (X : ℝ≥0 → Ω → OnePoint (Cone d)),
      SolvesMP (fun (F : 𝓢(Mat d, ℝ)) => extΔ (fun z : Cone d => F (z : Mat d)))
        (fun F => extΔ (AffinePSD.Necessity.Asharp χ P F)) (x : OnePoint (Cone d)) Pr X := by sorry

end AffinePSD.Existence
