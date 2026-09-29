-- Prove2me | Theorems.Thm_AlgebraicClosure_stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
-- name    : AlgebraicClosure.stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/aa9f0b59-aaec-52d9-afdc-c0c1231c05ca
-- title:
--   Open subgroups containing all inertia-with-ζ₃ contain Gal(ℚ̄/ℚ(ζ₃))
-- statement:
--   Let $\zeta$ be an element of $\overline{\mathbb{Q}}$ (the Lean algebraic closure of $\mathbb{Q}$) which is a primitive cube root of unity, and let $N$ be a subgroup of $G=\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})=\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ whose underlying set is open (for the Krull topology on $G$). Assume that for every natural number $q$ which is prime and every valuation subring $A$ of $\overline{\mathbb{Q}}$ such that the image of $q$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (the predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16)), the intersection of $N$ with $A$'s inertia subgroup viewed inside $G$ — that is, the image in $G$ of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$, as in [`ValuationSubring.inertiaSubgroupIn`](def/FLTPrelim_Ramification.html#L21) — contains the intersection of that inertia subgroup with the stabiliser of $\zeta$ for the natural action of $G$ on $\overline{\mathbb{Q}}$. The conclusion is that the full stabiliser of $\zeta$ in $G$, i.e. $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}(\zeta))$, is contained in $N$.
--
--   This is the relative, infinite-level statement that an open subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ which absorbs all inertia subgroups intersected with $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}(\zeta_3))$ already contains the whole of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}(\zeta_3))$; openness is what rules out the corresponding assertion for arbitrary subgroups. It feeds the vanishing-of-everywhere-unramified-extensions input [`ExtCitation.extVanishingCts_three`](thm.html#ExtCitation.extVanishingCts_three) over $\mathbb{Q}(\zeta_3)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le.lean

import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ValuationSubring

theorem AlgebraicClosure.stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3)
    (N : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))
    (hopen : IsOpen (N : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hN : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ⊓
        MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ ≤ N) :
    MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ ≤ N := by sorry
