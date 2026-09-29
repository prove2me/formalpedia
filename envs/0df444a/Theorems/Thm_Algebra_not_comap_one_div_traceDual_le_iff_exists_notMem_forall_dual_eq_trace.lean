-- Prove2me | Theorems.Thm_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace
-- name    : Algebra.not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/49afb80b-e7c8-5f72-a357-0a10966fba2c
-- title:
--   The different avoids a prime iff trace duality is perfect there
-- statement:
--   Fix an integrally closed Noetherian domain $A$ with fraction field $K$, and an integrally closed domain $B$ that is a finite free $A$-algebra, with fraction field $L$; the algebra structures are compatible ($L$ is a $K$-algebra and an $A$-algebra, with $A \to K \to L$ and $A \to B \to L$ scalar towers), and $L/K$ is separable. Let $P$ be a prime ideal of $B$. Write $C =$ `Submodule.traceDual A K (1 : Submodule B L)`, the $B$-submodule of $L$ consisting of those $c$ with $\operatorname{Tr}_{L/K}(c\,y)$ in the image of $A$ in $K$ for every $y$ in the unit submodule $1 \subseteq L$ (the image of $B$), and let $\mathfrak{D} \subseteq B$ be the preimage under $B \to L$ of the submodule quotient $1/C = \{x \in L : xC \subseteq 1\}$. The theorem asserts the equivalence: $\mathfrak{D}$ is not contained in $P$ if and only if there exists $s \notin P$ such that for every $A$-linear functional $\varphi : B \to A$ there is $x \in B$ with $\varphi(s\,y) = \operatorname{Tr}_{B/A}(x\,y)$ for all $y \in B$.
--
--   This is the local criterion for the Dedekind different $\mathfrak{D}_{B/A}$ in the AKLB setting: avoiding the prime $P$ is the same as the trace map $B \to \operatorname{Hom}_A(B,A)$, $x \mapsto \operatorname{Tr}_{B/A}(x\,\cdot)$, becoming surjective after multiplying the source functionals by a single element $s \notin P$. It feeds the characterisation of unramifiedness at $P$ in terms of the different, [`Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed`](thm.html#Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime] :
    ¬ ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L) ≤ P) ↔
      ∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y) := by sorry
