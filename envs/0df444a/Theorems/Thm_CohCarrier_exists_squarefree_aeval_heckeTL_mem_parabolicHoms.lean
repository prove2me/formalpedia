-- Prove2me | Theorems.Thm_CohCarrier_exists_squarefree_aeval_heckeTL_mem_parabolicHoms
-- name    : CohCarrier.exists_squarefree_aeval_heckeTL_mem_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/46553d13-cfd0-5d3e-ab94-b73264062625
-- title:
--   A squarefree polynomial sending H¹ into H¹ₚₐᵣ
-- statement:
--   Let $M$ be a nonzero natural number and $H$ a subgroup of $(\mathbb Z/M)^\times$, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb Z)$, namely the image in $\mathrm{SL}_2(\mathbb Z)$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb Z/M)^\times$ sending a matrix to the unit determined by its lower right entry modulo $M$. Let $\ell$ be a nonzero natural number which is prime and does not divide $M$. The module [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162) is the space of additive homomorphisms $\varphi$ from $\mathrm{Additive}\,\Gamma_H(M)$ to $\mathbb C$, i.e. of homomorphisms $\Gamma_H(M)\to\mathbb C$, and [`CohCarrier.heckeTL M H ℂ ℓ`](def/CohCarrier_Inst.html#L23) is the $\mathbb C$-linear endomorphism $T_\ell$ of this space obtained by restricting $\varphi$ along the conjugation homomorphism [`CohCarrier.conjL M H ℓ`](def/CohCarrier_Level.html#L228) from $\Gamma_H^{\mathrm{up}}(M,\ell)$ to $\Gamma_H(M)$ and then applying the transfer (corestriction) [`CohCarrier.coresAdd`](def/CohCarrier_Level.html#L63) of that finite-index subgroup back to $\Gamma_H(M)$. The assertion is that there exists a squarefree polynomial $p\in\mathbb C[X]$ such that for every $\varphi\in$ [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162) the homomorphism $p(T_\ell)\varphi$ lies in [`ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ`](def/ModularCurve_PeriodMap.html#L62), that is, $p(T_\ell)\varphi$ vanishes on every $\gamma\in\Gamma_H(M)$ whose integral matrix has trace with square $4$.
--
--   This is the semisimplicity of the Hecke operator $T_\ell$, for $\ell$ prime to the level, on the boundary (Eisenstein) quotient $H^1(\Gamma_H(M),\mathbb C)/H^1_{\mathrm{par}}(\Gamma_H(M),\mathbb C)$, expressed as the existence of a single squarefree polynomial carrying all of $H^1$ into the parabolic part. It is used in the construction of the period map, via [`CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero`](thm.html#CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_squarefree_aeval_heckeTL_mem_parabolicHoms.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_squarefree_aeval_heckeTL_mem_parabolicHoms
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∃ p : Polynomial ℂ, Squarefree p ∧
      ∀ φ : CohCarrier.H1 M H ℂ,
        Polynomial.aeval (CohCarrier.heckeTL M H ℂ ℓ) p φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by sorry
