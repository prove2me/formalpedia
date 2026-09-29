-- Prove2me | Theorems.Thm_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq
-- name    : CuspidalType.exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5f9c3924-0961-54dc-9963-12a3c5b8f20c
-- title:
--   Exactly q+1 characters of 𝔽_{q²}^× trivial on 𝔽_q^×
-- statement:
--   Let $q$ be a prime and let $K$ be an algebraically closed field of characteristic zero. The assertion is that there exists a finite set $S_0$ of monoid homomorphisms $\mu\colon (\mathbb{F}_{q^2})^\times \to K^\times$, where $\mathbb{F}_{q^2}$ is `GaloisField q 2`, with two properties. First, a homomorphism $\mu\colon (\mathbb{F}_{q^2})^\times \to K^\times$ belongs to $S_0$ if and only if $\mu$ is trivial on the image of the prime field units, i.e. $\mu(\iota(c)) = 1$ for every $c \in (\mathbb{Z}/q)^\times$, where $\iota$ is the map on unit groups induced by the structure morphism $\mathbb{Z}/q \to \mathbb{F}_{q^2}$. Second, the cardinality of $S_0$ is $q+1$. Thus the characters of $(\mathbb{F}_{q^2})^\times$ with values in $K^\times$ that restrict trivially to $\mathbb{F}_q^\times$ form a finite set, exhibited as a `Finset` by the membership criterion above, of exactly $q+1$ elements; the existential form is used because the full character group carries no finiteness instance.
--
--   This is the count of the characters of the cyclic quotient $\mathbb{F}_{q^2}^\times/\mathbb{F}_q^\times$, a group of order $q+1$, with values in an algebraically closed field of characteristic zero. It supplies the index set of characters from which the cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$ attached to the non-split torus are parametrised, and is used in the construction of a representation of the prescribed cuspidal type and in the computation of characteristic polynomials on the non-split torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∃ S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ),
      (∀ μ : (GaloisField q 2)ˣ →* Kˣ,
        μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) ∧
      S₀.card = q + 1 := by sorry
