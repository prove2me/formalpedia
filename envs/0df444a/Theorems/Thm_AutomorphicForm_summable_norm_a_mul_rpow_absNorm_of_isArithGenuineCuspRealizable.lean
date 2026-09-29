-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
-- name    : AutomorphicForm.summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9917c2eb-f6af-5868-b7af-616a23c21482
-- title:
--   First-moment bound sumₚ |aₚ| Np^{-σ}<∞ for σ>1
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, that is, a nonzero ideal $\Phi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with two functions $p \mapsto \Phi.a\,p$ and $p \mapsto \Phi.b\,p$ from the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ to $\mathbb{C}$. Assume $\Phi$ is arithmetically genuinely cuspidally realizable at the general production pins, i.e. the centrally renormalised eigensystem $\Phi.\mathrm{toRawCentral}$ — same level and same $a$, with $b$ replaced by $v \mapsto (\mathrm{cNorm}\,v)^{-1}\Phi.b\,v$ — admits a smooth cuspidal realization $R$ at the carrier pins $\mathrm{productionPinsGeneral}\ \mathbb{Q}$ (the pins built from the class-representative Siegel set with parameters $c = 1/2$, $u = 1$, $d_1 = 1/2$, $d_2 = 2$, the level subgroups $\mathrm{levelOne} \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}$ and the adelic box) such that $R$ is genuine. Let $SQ_0$ be a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ and suppose $\|\Phi.b\,p\| = 1$ for every $p \notin SQ_0$. Then for every real $\sigma > 1$ the family $p \mapsto \|\Phi.a\,p\|\cdot (\mathrm{absNorm}\,p)^{-\sigma}$, indexed by the height-one spectrum, is summable.
--
--   This is the first-moment (Rankin–Selberg plus Cauchy–Schwarz type) absolute convergence bound for the Hecke eigenvalues of a unitarily normalised automorphic eigensystem over $\mathbb{Q}$; the trivial Hecke estimate would only give convergence for $\sigma > 3/2$, so the automorphic input is essential. It serves as the analytic hypothesis in the Rankin–Selberg transport step of the converse direction of Langlands–Tunnell, being used in the construction of a nicely pinned twisted datum with prescribed Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable.lean

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse

theorem AutomorphicForm.summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) := by sorry
