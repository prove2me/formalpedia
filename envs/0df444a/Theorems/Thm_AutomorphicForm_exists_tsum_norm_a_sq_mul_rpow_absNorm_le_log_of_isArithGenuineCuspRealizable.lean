-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
-- name    : AutomorphicForm.exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/fa1b0bf7-8799-50c4-806e-9a9ac074a43e
-- title:
--   Rankin's logarithmic second-moment bound for Hecke eigenvalues
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, that is, a nonzero ideal $\Phi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with two functions $p \mapsto \Phi.a\,p$ and $p \mapsto \Phi.b\,p$ on the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ with values in $\mathbb{C}$. Assume `IsArithGenuineCuspRealizable` for $\Phi$ at the carrier pins `productionPinsGeneral ℚ`: there exists a smooth cusp realisation at these pins of the re-normalised eigensystem $\Phi$`.toRawCentral`, which has the same level and the same $a$ but whose $b$ at a place $v$ is $(\mathrm{cNorm}\,v)^{-1}\,\Phi.b\,v$, and this realisation is genuine in the sense of `IsGenuineCuspRealizationAt`. Here `productionPinsGeneral ℚ` is the `CarrierPins` record — a measurable space and measure on the adelic $\mathrm{GL}_2$, a domain $D$, a central subgroup, level subgroups, Hecke generators at the finite places, and a measurable space and measure on the adele ring — obtained from the class-representative Siegel set with parameters $c = 1/2$, $u = 1$, $d_1 = 1/2$, $d_2 = 2$, the subgroups $N \mapsto \mathrm{levelOne}\,N \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the generators $\mathrm{heckeGen}$, and the adelic box. Assume further that there is a finite set $SQ_0$ of height-one primes outside which $\lVert \Phi.b\,p \rVert = 1$. Then there is a real constant $C$ such that for every real $\sigma$ with $1 < \sigma < 2$ the family $p \mapsto \lVert \Phi.a\,p \rVert^2 \,\mathrm{N}(p)^{-\sigma}$, indexed by all height-one primes of $\mathcal{O}_{\mathbb{Q}}$ with $\mathrm{N}(p)$ the absolute ideal norm, is summable and $$\sum_p \lVert \Phi.a\,p \rVert^2\, \mathrm{N}(p)^{-\sigma} \le \log\frac{1}{\sigma - 1} + C.$$
--
--   This is Rankin's second-moment estimate for the Hecke eigenvalues of a cuspidal eigensystem on $\mathrm{GL}_2$ over $\mathbb{Q}$ with unitary central character, in the form used by Deligne and Serre; the constant $1$ in front of $\log\frac{1}{\sigma-1}$ is what distinguishes a cuspidal system from one coming from a reducible two-dimensional representation. It is applied in the weight-one step, where it is specialised to the eigensystem attached to a weight-one Hecke eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ < 2 →
      Summable (fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ)) ∧
      ∑' p : HeightOneSpectrum (𝓞 ℚ), ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) ≤
        Real.log (1 / (σ - 1)) + C := by sorry
