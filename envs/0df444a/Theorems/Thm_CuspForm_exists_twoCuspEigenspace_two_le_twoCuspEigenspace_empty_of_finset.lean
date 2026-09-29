-- Prove2me | Theorems.Thm_CuspForm_exists_twoCuspEigenspace_two_le_twoCuspEigenspace_empty_of_finset
-- name    : CuspForm.exists_twoCuspEigenspace_two_le_twoCuspEigenspace_empty_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/e5f79cb8-d912-54ad-b786-56ef37c93375
-- title:
--   Completing a mod-π Hecke eigensystem away from S
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$, and $H$ a subgroup of $(\mathbb{Z}/M)^\times$. Let $S$ be a finite set of natural numbers, $A$ a subring of $\mathbb{C}$ and $\pi \in A$ such that the principal ideal $(\pi) = \mathrm{span}\,\{\pi\}$ is maximal in $A$ and contains $p$. Write $\kappa = A/(\pi)$. Recall that for a set $S$ of primes the generator type [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) has constructors `T ℓ` for primes $\ell \notin S$ with $\ell \nmid M$, `U q` for primes $q \mid M$, and `dia d` for $d \in (\mathbb{Z}/M)^\times$; for a function $\chi$ from these generators to $\kappa$, [`CuspForm.twoCuspEigenspace`](def/CuspForm_TwoCuspLattice.html#L210) is the $\kappa$-submodule of [`CuspForm.TwoCuspForms M H 2 p A (π)`](def/CuspForm_TwoCuspLattice.html#L133), the quotient of the weight-two two-cusp lattice at $p$ with coefficients in $A$ by $(\pi)\cdot\top$, consisting of those $\omega$ with $\mathrm{twoCuspGenMod}\,g\,\omega = \chi(g)\cdot\omega$ for every generator $g$. Given such a $\chi$ on `Gen M S`, the assertion is that there is a $\chi'$ on `Gen M ∅`, that is on all of $T_\ell$ ($\ell$ prime, $\ell \nmid M$), $U_q$ ($q$ prime, $q \mid M$) and $\langle d\rangle$, which agrees with $\chi$ on $T_\ell$ for every prime $\ell \notin S$ with $\ell \nmid M$, on every $U_q$ and on every $\langle d\rangle$, and for which the eigenspace for $\chi$ relative to $S$ is contained in the eigenspace for $\chi'$ relative to $\emptyset$.
--
--   This is the weight-two case of Ribet's lemma on the existence of eigenvalues for the missing Hecke operators: on simultaneous eigenvectors for the operators away from $S$, each $T_\ell$ with $\ell \in S$, $\ell \nmid M$, acts by a single scalar. It feeds the multiplicity-one argument on the Tate module of $J_H(M)$, being cited by the statement that an ordinary non-Eisenstein eigensystem lying in the relevant subgroup acts as required on the multiplicative part of that Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_twoCuspEigenspace_two_le_twoCuspEigenspace_empty_of_finset.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_twoCuspEigenspace_two_le_twoCuspEigenspace_empty_of_finset
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (S : Finset ℕ) (A : Subring ℂ) (π : A) (hmax : (Ideal.span ({π} : Set A)).IsMaximal)
    (hp : (p : A) ∈ Ideal.span ({π} : Set A))
    (χ : CohCarrier.Gen M (↑S : Set ℕ) → A ⧸ Ideal.span ({π} : Set A)) :
    ∃ χ' : CohCarrier.Gen M (∅ : Set ℕ) → A ⧸ Ideal.span ({π} : Set A),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
          χ' (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM) = χ (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M),
          χ' (CohCarrier.Gen.U q hq hqM) = χ (CohCarrier.Gen.U q hq hqM)) ∧
      (∀ d : (ZMod M)ˣ, χ' (CohCarrier.Gen.dia d) = χ (CohCarrier.Gen.dia d)) ∧
      CuspForm.twoCuspEigenspace (M := M) (H := H) (k := 2) (p := p) (Ideal.span ({π} : Set A)) ↑S χ ≤
        CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ∅ χ' := by sorry
