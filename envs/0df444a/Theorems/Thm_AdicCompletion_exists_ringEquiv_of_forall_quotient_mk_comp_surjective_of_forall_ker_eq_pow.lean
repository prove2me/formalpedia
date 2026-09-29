-- Prove2me | Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
-- name    : AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/343e3c5d-d522-5d53-84bf-b5fee11a7593
-- title:
--   Levelwise isomorphic truncations give isomorphic adic completions
-- statement:
--   Let $R$ and $S$ be commutative rings, $I \subseteq R$ and $J \subseteq S$ ideals, and $f \colon R \to S$ a ring homomorphism. Assume that for every natural number $k$ the composite $R \xrightarrow{f} S \to S/J^{k}$ is surjective, and that for every $k$ the kernel of this composite is exactly $I^{k}$. The conclusion asserts the existence of a ring isomorphism $e \colon \widehat{R}_{I} \to \widehat{S}_{J}$ between the $I$-adic completion of $R$ and the $J$-adic completion of $S$ (Mathlib's `AdicCompletion`, the inverse limit of the truncations), such that for every $r \in R$ one has $e(\iota_{R}(r)) = \iota_{S}(f(r))$, where $\iota_{R}$ and $\iota_{S}$ denote the canonical algebra maps $R \to \widehat{R}_{I}$ and $S \to \widehat{S}_{J}$. Thus $e$ is compatible with $f$ on the images of the structure maps; note that the isomorphism is produced existentially, not as a named construction, and no Noetherian, local or finiteness hypothesis is imposed.
--
--   This is the standard 'isomorphic truncations imply isomorphic completions' step, in the form needed when a ring map identifies all the finite levels $R/I^{k} \cong S/J^{k}$. It is used in the project to compare adic completions of local rings and of stalks on integral models of modular curves, for instance by [`AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType`](thm.html#AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType), [`IsLocalRing.exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective`](thm.html#IsLocalRing.exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective) and the identification of a stalk completion on the $X_1$ crossing model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ k)).comp f))
    (hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (J ^ k)).comp f) = I ^ k) :
    ∃ e : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, e (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by sorry
