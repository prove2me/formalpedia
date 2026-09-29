-- Prove2me | Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one
-- name    : ExtCitation.exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/d8ec2320-1047-520c-9f5c-490c3d657fbc
-- title:
--   Triviality of χₚ on Gal(ℚ̄_q/K) forces μₚ ⊂ K
-- statement:
--   Let $q$ and $p$ be primes and let $K$ be an intermediate field of the extension $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$, where $\overline{\mathbb{Q}}_q$ denotes the fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$. Assume that every $\mathbb{Q}_q$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_q$ lying in the fixing subgroup of $K$ (that is, fixing $K$ pointwise) satisfies $\chi_p(\mathrm{res}(\sigma)) = 1$ in $(\mathbb{Z}/p)^{\times}$; here $\mathrm{res} =$ [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) is the homomorphism sending $\sigma$ to its restriction of scalars to a $\mathbb{Q}$-algebra automorphism followed by restriction along the normal subextension $\overline{\mathbb{Q}} \subset \overline{\mathbb{Q}}_q$, and $\chi_p =$ `cycloChar p` is the mod $p$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained from Mathlib's `modularCyclotomicCharacter` of $\overline{\mathbb{Q}}$ at $p$. The conclusion is that there is an element $\zeta$ of $K$ which is a primitive $p$-th root of unity, i.e. $\zeta^p = 1$ and $\zeta$ has exact order $p$ in the sense of `IsPrimitiveRoot`.
--
--   This is the Galois-correspondence half of the statement that a local subextension on which the mod $p$ cyclotomic character is trivial contains $\mu_p$. It is used in the verification that the relevant level contains the $p$-th roots of unity, via [`groupCohomology.bijective_theta1_of_trivial_line_of_isOpen`](thm.html#groupCohomology.bijective_theta1_of_trivial_line_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation

theorem ExtCitation.exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (hK : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, σ ∈ K.fixingSubgroup → cycloChar p (localGaloisToGlobal q σ) = 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by sorry
