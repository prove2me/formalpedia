-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime
-- name    : ExtCitation.LocalLevel.exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/095c810d-5e79-53db-8367-8a84a8907aa3
-- title:
--   Inertia at q moves an e-th root of q
-- statement:
--   Let $q$ be a prime and $e$ an integer with $2 \le e$ and $q \nmid e$, and let $\alpha$ be an element of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $\alpha^{e} = q$. The assertion is that there is a $\mathbb Q_{q}$-algebra automorphism $t$ of the algebraic closure $\mathrm{PadicAlgCl}\,q$ of $\mathbb Q_{q}$ whose image $\sigma =$ [`localGaloisToGlobal q t`](def/GaloisRep_CompletionBridge.html#L41) in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ — obtained by restricting scalars from $\mathbb Q_{q}$ to $\mathbb Q$ and then restricting the resulting automorphism to the normal subextension $\overline{\mathbb Q}$ — has two properties: first, $\sigma$ lies in `(padicPlace q).inertiaSubgroupIn ℚ`, that is, in the image, under the inclusion of the decomposition subgroup of the valuation subring [`padicPlace q`](def/GaloisRep_CompletionBridge.html#L25) into the full group $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, of the inertia subgroup of that valuation subring, where [`padicPlace q`](def/GaloisRep_CompletionBridge.html#L25) is the pullback along the fixed $\mathbb Q$-embedding $\overline{\mathbb Q} \hookrightarrow \mathrm{PadicAlgCl}\,q$ of the valuation subring of the $q$-adic absolute value on $\mathrm{PadicAlgCl}\,q$; and second, $\sigma(\alpha) \neq \alpha$.
--
--   This is the statement that $\mathbb Q_{q}(q^{1/e})$ is ramified over $\mathbb Q_{q}$ for $e \ge 2$ prime to $q$, packaged so that the moving element is produced inside the local Galois group at $q$ and then transported to the inertia subgroup of the chosen place of $\overline{\mathbb Q}$. It is used for the divisibility criterion [`ExtCitation.LocalLevel.dvd_of_forall_inertia_apply_pow_eq`](thm.html#ExtCitation.LocalLevel.dvd_of_forall_inertia_apply_pow_eq), for the construction of a nontrivial Kummer character in [`ExtCitation.exists_kummerCharacter_ne_one`](thm.html#ExtCitation.exists_kummerCharacter_ne_one), and, in the case $e = 2$, for [`ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ExtCitation.LocalLevel.exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime (q : ℕ) [Fact q.Prime] {e : ℕ} (he : 2 ≤ e) (hqe : ¬ q ∣ e)
    {α : AlgebraicClosure ℚ} (hα : α ^ e = (q : AlgebraicClosure ℚ)) :
    ∃ t : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      localGaloisToGlobal q t ∈ (padicPlace q).inertiaSubgroupIn ℚ ∧ localGaloisToGlobal q t α ≠ α := by sorry
