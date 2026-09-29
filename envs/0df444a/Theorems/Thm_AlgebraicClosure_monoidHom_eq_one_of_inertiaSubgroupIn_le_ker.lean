-- Prove2me | Theorems.Thm_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker
-- name    : AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/bfdcd8d4-24ac-5ffb-b064-51c0c7bf2d65
-- title:
--   Characters of G_ℚ unramified everywhere are trivial
-- statement:
--   Let $\Gamma$ be a group and let $\chi$ be a monoid homomorphism from the group of field automorphisms of `AlgebraicClosure ℚ` over $\mathbb Q$, i.e. from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, to $\Gamma$. Assume two hypotheses. First, the kernel of $\chi$, viewed as a subset of the automorphism group, is open for the topology on that group. Second, $\chi$ is unramified at every finite place in the following sense: for every natural number $q$ that is prime and every valuation subring $A$ of `AlgebraicClosure ℚ` such that the image of $q$ in $\overline{\mathbb Q}$ lies in the nonunits of $A$, the subgroup `A.inertiaSubgroupIn ℚ` — the image of the inertia subgroup of $A$ over $\mathbb Q$ under the inclusion of the decomposition subgroup of $A$ over $\mathbb Q$ into the full automorphism group — is contained in the kernel of $\chi$. The conclusion is that $\chi$ is the trivial homomorphism, $\chi = 1$; that is, $\chi(\sigma) = 1$ for every automorphism $\sigma$ of $\overline{\mathbb Q}$ over $\mathbb Q$.
--
--   This is the character form of the statement that $\mathbb Q$ admits no nontrivial everywhere-unramified finite extension, the classical consequence of Minkowski's discriminant bound; it packages the subgroup version for use in arguments where an everywhere-unramified character must be shown to vanish. Within the present development it is invoked in [`RibetIrr.exists_dickson_eval_eq_of_span_ne_top`](thm.html#RibetIrr.exists_dickson_eval_eq_of_span_ne_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker {Γ : Type*} [Group Γ]
    (χ : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* Γ)
    (hopen : IsOpen (χ.ker : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ≤ χ.ker) :
    χ = 1 := by sorry
