-- Prove2me | Theorems.Thm_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber
-- name    : Algebra.exists_notMem_forall_dual_eq_trace_iff_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/5dba8739-f058-59e6-9f17-5efdcf823978
-- title:
--   Perfectness of the trace pairing at a prime descends to the fibre
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra that is finite and free as an $A$-module, let $p$ be a prime ideal of $A$ and $P$ a prime ideal of $B$ lying over $p$. Write $p.\mathrm{Fiber}\ B$ for the base change of $B$ along the residue field $\kappa(p) = A_p/pA_p$, and let $P'$ be a prime ideal of this fibre such that $P$ is the contraction of $P'$ along the canonical algebra map $B \to p.\mathrm{Fiber}\ B$ given by `Algebra.TensorProduct.includeRight`. The assertion is the equivalence of the following two conditions. First: there exists $s \in B$ with $s \notin P$ such that for every $A$-linear functional $\varphi \colon B \to A$ there is an $x \in B$ with $\varphi(sy) = \mathrm{Tr}_{B/A}(xy)$ for all $y \in B$. Second: there exists $s$ in $p.\mathrm{Fiber}\ B$ with $s \notin P'$ such that for every $\kappa(p)$-linear functional $\varphi$ on $p.\mathrm{Fiber}\ B$ there is an $x$ in $p.\mathrm{Fiber}\ B$ with $\varphi(sy) = \mathrm{Tr}_{(p.\mathrm{Fiber}\ B)/\kappa(p)}(xy)$ for all $y$ in the fibre. In each case the condition says that the trace map $x \mapsto \mathrm{Tr}(x\,\cdot\,)$ into the linear dual becomes surjective after multiplying by a single element outside the given prime.
--
--   This is the base-change step in the local theory of the trace form: surjectivity of the trace map into the dual, localised at $P$, is detected on the fibre of $B$ over the residue field of $p$, which reduces a question about a finite free algebra over $A$ to one about a finite-dimensional algebra over a field. It is used in the proof of [`Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed`](thm.html#Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed), where unramifiedness at a prime is characterised in terms of the inverse different.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.exists_notMem_forall_dual_eq_trace_iff_fiber
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (P' : Ideal (p.Fiber B)) [P'.IsPrime]
    (hP' : P = P'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
      (∃ s ∉ P', ∀ φ : Module.Dual p.ResidueField (p.Fiber B), ∃ x : p.Fiber B, ∀ y : p.Fiber B,
        φ (s * y) = Algebra.trace p.ResidueField (p.Fiber B) (x * y)) := by sorry
