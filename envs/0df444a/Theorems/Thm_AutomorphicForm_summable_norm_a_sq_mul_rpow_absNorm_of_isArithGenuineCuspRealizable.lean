-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
-- name    : AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/2d8dd5f7-f4ba-59be-93c1-539b53be4590
-- title:
--   Rankin–Selberg second moment for cusp-realizable eigensystems over ℚ
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, that is, a nonzero ideal $\Phi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with two functions $p \mapsto \Phi.a\,p$ and $p \mapsto \Phi.b\,p$ from the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$ to $\mathbb{C}$. Assume [`AutomorphicForm.IsArithGenuineCuspRealizable`](def/AutomorphicForm_ProductionPinsGeneral.html#L398) for $\Phi$ at the pins [`AutomorphicForm.productionPinsGeneral ℚ`](def/AutomorphicForm_ProductionPinsGeneral.html#L307): the centrally renormalised eigensystem `Φ.toRawCentral` — same level and same $a$, with $b$ replaced by $v \mapsto (\mathrm{cNorm}\,v)^{-1}\,\Phi.b\,v$ — admits a realization $R$ of type `SmoothCuspRealizationAt` at those pins which satisfies the predicate `IsGenuineCuspRealizationAt`; here the pins are the carrier data `productionPinsGeneralOf ℚ (1/2) 1 (1/2) 2`, built from the class-representative Siegel set `classRepSiegelSet ℚ (1/2) 1 (1/2) 2` as fundamental domain, the level subgroups $N \mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, the local Hecke generators `heckeGen (𝓞 ℚ) ℚ v`, and the adelic box `adelicBox ℚ`. Assume further that a finite set $SQ_0$ of height one primes is given with $\|\Phi.b\,p\| = 1$ for every $p \notin SQ_0$. The conclusion is that for every real $\sigma > 1$ the family $p \mapsto \|\Phi.a\,p\|^2 \cdot N(p)^{-\sigma}$, indexed by all height one primes $p$ of $\mathcal{O}_{\mathbb{Q}}$ with $N(p) =$ `Ideal.absNorm p.asIdeal` and the power taken as a real power, is summable.
--
--   This is the prime part of the absolute convergence, in the half-plane $\operatorname{Re} s > 1$, of the Rankin–Selberg convolution of a cuspidal eigensystem with its own conjugate, expressed as a second-moment bound on the Hecke eigenvalues $a_p$ under the unitary normalisation $\|b_p\| = 1$ outside a finite set. It feeds the corresponding first-moment statement [`AutomorphicForm.summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.summable_norm_a_mul_rpow_absNorm_of_isArithGenuineCuspRealizable), obtained from it by Cauchy–Schwarz, within the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ) := by sorry
