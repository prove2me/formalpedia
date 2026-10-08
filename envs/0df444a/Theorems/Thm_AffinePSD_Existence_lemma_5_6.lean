-- Prove2me | Theorems.Thm_AffinePSD_Existence_lemma_5_6
-- name    : AffinePSD.Existence.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:04.147111+00:00
-- url     : https://prove2.me/theorems/1ca4d88b-a692-45ce-9f43-d1345750d4b4
-- title:
--   Lemma 5.6 — an S_d^+-valued càdlàg solution of the martingale problem for A^{ε,δ,n} from every x
-- statement:
--   Let $(\alpha,b,\beta^{ij},c=0,\gamma=0,m,\mu)$ be an admissible parameter set, fix $\varepsilon,\delta>0$ and $n\in\mathbb N$, and let $\phi_n,\eta_\varepsilon$ be cut-offs as in (5.4) and §5.2. Then for every $x\in S_d^+$ there is an $S_d^+$-valued càdlàg process $X$ with $X_0=x$ such that
--   $$f(X_t)-\int_0^t\mathcal A^{\varepsilon,\delta,n}f(X_s)\,ds$$
--   is a martingale for every rapidly decreasing $f$ on $S_d$. Moreover the integrands of (5.10) are integrable.
--
--   These regularized solutions are the approximations from which Lemma 5.8 builds a solution for $\mathcal A$.
--
--   **Formalization Note** The probability space is existentially quantified, and $X$ is a martingale-problem solution in the sense of `SolvesMP` (natural filtration, $X_0=x$ almost surely, càdlàg paths in time $\mathbb R_{\ge0}$). The test functions are restrictions to the cone of Schwartz functions on $M_d$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 5.6, p. 44

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Existence_Regularization
import Definitions.Def_AffinePSD_Existence_MartingaleProblem

open MeasureTheory
open scoped NNReal SchwartzMap

namespace AffinePSD.Existence

/-- Lemma 5.6 (arXiv:0910.0137v3, §5.2, p. 44): under the standing assumptions of §5.2 (an
admissible parameter set with `c = 0`, `γ = 0`; `ε, δ > 0`, `n ∈ ℕ` fixed, p. 41), for every
`x ∈ S_d^+` there is an `S_d^+`-valued càdlàg solution `X` of the martingale problem for
`A^{ε,δ,n}` with `X_0 = x`: `f(X_t) − ∫_0^t A^{ε,δ,n} f(X_s) ds` is a martingale for all `f ∈ S`.
Formalization Note: `ϕ_n`, `η_ε` are any cut-offs with the properties (5.4) and p. 42; the
probability space is existentially quantified; `f ∈ S` ranges over restrictions of Schwartz
functions on `M_d`; the martingale property is for the natural filtration of `X` (`SolvesMP`);
càdlàg is `EthierKurtz.HasCadlagPaths` with time in `ℝ≥0`; `RegIntegrable` (the integrands of
(5.10) are integrable) guards against Lean's junk value of a non-integrable Bochner integral. -/
theorem lemma_5_6 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.Admissible χ P)
    (hc : P.c = 0) (hγ : P.γ = 0) (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (ϕ η : Mat d → ℝ) (hϕ : IsPhiN n ϕ) (hη : IsEtaEps ε η) (x : Cone d) :
    RegIntegrable χ P ϕ δ ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pr : Measure Ω) (X : ℝ≥0 → Ω → Cone d),
      SolvesMP (fun (F : 𝓢(Mat d, ℝ)) (z : Cone d) => F (z : Mat d))
        (fun F (z : Cone d) => Areg χ P ϕ η ε δ F z) x Pr X := by sorry

end AffinePSD.Existence
