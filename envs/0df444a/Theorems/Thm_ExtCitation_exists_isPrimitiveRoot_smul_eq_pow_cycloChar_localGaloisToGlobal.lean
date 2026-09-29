-- Prove2me | Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
-- name    : ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a98e787b-957f-50f6-8209-a29ac62b9f13
-- title:
--   Galois action on μₚ ⊂ ℚ̄_q via the cyclotomic character
-- statement:
--   Let $q$ and $p$ be primes. Writing $\overline{\mathbb{Q}}_q$ for `PadicAlgCl q`, the assertion is that there exists a unit $\zeta$ of $\overline{\mathbb{Q}}_q$ which is a primitive $p$-th root of unity in the group $\overline{\mathbb{Q}}_q^{\times}$ (in the sense of `IsPrimitiveRoot`), such that for every $\mathbb{Q}_q$-algebra automorphism $g$ of $\overline{\mathbb{Q}}_q$ one has $g \cdot \zeta = \zeta^{\,n(g)}$, the left-hand side being the natural action of $g$ on units and the exponent $n(g)$ being the canonical natural-number representative in $\{0,\dots,p-1\}$ of the element $\mathrm{cycloChar}\,p\,(\mathrm{localGaloisToGlobal}\,q\,g)$ of $(\mathbb{Z}/p)^{\times}$. Here [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) is the homomorphism from $\mathrm{Aut}_{\mathbb{Q}_q}(\overline{\mathbb{Q}}_q)$ to $\mathrm{Aut}_{\mathbb{Q}}(\mathrm{AlgebraicClosure}\ \mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, and `cycloChar p` is the mod $p$ cyclotomic character of $\mathrm{Aut}_{\mathbb{Q}}(\mathrm{AlgebraicClosure}\ \mathbb{Q})$, namely the monoid homomorphism to $(\mathbb{Z}/p)^{\times}$ given by Mathlib's `modularCyclotomicCharacter` for the group $\mu_p$ of $p$-th roots of unity of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$.
--
--   This records that the local Galois group at $q$ acts on a suitable copy of $\mu_p$ inside $\overline{\mathbb{Q}}_q$ through the mod $p$ cyclotomic character of the global Galois group, pulled back along [`localGaloisToGlobal`](def/GaloisRep_CompletionBridge.html#L41); no condition relating $p$ and $q$ is imposed. It supplies the root of unity required by the passage between additive and multiplicative cocycles for $\mu_p$-valued local cohomology, and is used in the construction of unipotent models and of local flat deformation classes for residual Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal.lean

import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation

theorem ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] :
    ∃ ζ : (PadicAlgCl q)ˣ, IsPrimitiveRoot ζ p ∧ ∀ g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      g • ζ = ζ ^ (cycloChar p (localGaloisToGlobal q g) : ZMod p).val := by sorry
