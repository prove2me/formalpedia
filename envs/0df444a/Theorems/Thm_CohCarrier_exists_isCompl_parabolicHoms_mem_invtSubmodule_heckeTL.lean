-- Prove2me | Theorems.Thm_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL
-- name    : CohCarrier.exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/b4fe38c7-3ff4-5b46-98a8-090a0af1dae3
-- title:
--   Manin–Drinfeld: Hecke-stable complement of the parabolic part
-- statement:
--   Fix a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a prime $\ell$ with $\ell \nmid M$. Let $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower-right entry modulo $M$, and let $H^1 =$ [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162) be the $\mathbb{C}$-vector space of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(M) \to \mathbb{C}$, i.e. of homomorphisms from $\Gamma_H(M)$ to $\mathbb{C}$. Inside it sits the submodule [`ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ`](def/ModularCurve_PeriodMap.html#L62) of those $\varphi$ vanishing on every $\gamma \in \Gamma_H(M)$ whose matrix satisfies $(\mathrm{tr}\,\gamma)^2 = 4$, and the $\mathbb{C}$-linear endomorphism [`CohCarrier.heckeTL M H ℂ ℓ`](def/CohCarrier_Inst.html#L23), which sends $\varphi$ to the transfer (corestriction) along a finite-index subgroup of the composite of $\varphi$ with the conjugation homomorphism [`CohCarrier.conjL M H ℓ`](def/CohCarrier_Level.html#L228) into $\Gamma_H(M)$. The assertion is that there exists a $\mathbb{C}$-subspace $Q \subseteq H^1$ which is a complement of the parabolic subspace (their intersection is zero and their sum is all of $H^1$) and which is invariant under [`CohCarrier.heckeTL M H ℂ ℓ`](def/CohCarrier_Inst.html#L23).
--
--   This is the Manin–Drinfeld splitting in its group-cohomological form: over $\mathbb{C}$ the parabolic subspace of $H^1(\Gamma_H(M), \mathbb{C})$ admits a complement stable under the transfer Hecke operator at a prime $\ell$ not dividing the level. It is used in the proof of [`CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero`](thm.html#CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero), where the splitting allows the action of $T_\ell$ on the two factors to be analysed separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_isCompl_parabolicHoms_mem_invtSubmodule_heckeTL
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∃ Q : Submodule ℂ (CohCarrier.H1 M H ℂ),
      IsCompl (ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) Q ∧
      Q ∈ Module.End.invtSubmodule (CohCarrier.heckeTL M H ℂ ℓ) := by sorry
