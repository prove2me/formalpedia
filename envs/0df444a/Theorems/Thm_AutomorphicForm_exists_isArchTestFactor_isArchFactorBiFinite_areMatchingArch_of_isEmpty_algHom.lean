-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
-- name    : AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a12d487a-10ac-5ea8-b4d7-bda68d56acdd
-- title:
--   Archimedean matching factor when L does not embed in K_∞
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and assume $[L:K]=2$ or $[L:K]=3$. Let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, and assume that there is no $K$-algebra homomorphism from $L$ into the infinite adele ring $K_\infty =$ `InfiniteAdeleRing K`. Let $\mathrm{tys}_L$ be an `ArchTypeFamily` for $L$, that is, an assignment to each infinite place $w$ of $L$ of a natural number $m_w$ together with, for each $i < m_w$, a pair consisting of $n \in \mathbb{N}$ and a complex representation of `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$. Let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ satisfy `IsArchTestFactor`, i.e. $\varphi_a$ has compact support and there is a function $\Phi$ on $2\times 2$ matrices over the mixed space of $L$, of class $C^\infty$ over $\mathbb{R}$, with $\varphi_a(g) = \Phi(\mathrm{archEntries}(g))$, the entries of $g$ being transported along the ring equivalence between $L_\infty$ and the mixed space; and assume $\varphi_a$ is bi-finite for $\mathrm{tys}_L$, meaning that $g \mapsto \varphi_a(g^{-1})$ lies in the intersection over infinite places $w$ of the join of the submodules `archFactorTypeSubmoduleAt` attached to the types listed at $w$, and $\varphi_a$ lies in the corresponding submodule built from `archFactorDualTypeSubmoduleAt`. Then there exist an `ArchTypeFamily` $\mathrm{tys}_K$ for $K$ and a function $f_a : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ satisfying the same two conditions over $K$ and matching $\varphi_a$ archimedeanly: with respect to the chosen Haar measures on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and $\mathrm{GL}_2(K_\infty)$, for every $\delta \in \mathrm{GL}_2(L \otimes_K K_\infty)$ whose norm string is regular semisimple, every regular semisimple $\gamma \in \mathrm{GL}_2(K_\infty)$, every norm conjugator $y$ relating them, and every pair of Haar measures on the centraliser of $\gamma$ and on the $\sigma$-twisted centraliser of $\delta$ which is coupled via $y$, any value of the $\sigma$-twisted orbital integral at $\delta$ of $\varphi_a$ composed with the map $\mathrm{GL}_2(L \otimes_K K_\infty) \to \mathrm{GL}_2(L_\infty)$ equals any value of the orbital integral of $f_a$ at $\gamma$; and for every regular semisimple $\gamma$ that is not a norm, every value of the orbital integral of $f_a$ at $\gamma$ with respect to any Haar measure on its centraliser is $0$.
--
--   This is the archimedean transfer, or matching, of test functions for cyclic base change of $\mathrm{GL}_2$, in the case where $L$ admits no $K$-embedding into $K_\infty$; that emptiness hypothesis forces the degree to be $2$, so the degree-three alternative is vacuous, and the assertion follows from the degree-two case together with the uniqueness of ordinary and twisted orbital integrals at regular semisimple elements. It supplies the archimedean component in the construction of matching test functions at a principal level, which is what cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧ AreMatchingArch K L σ φa fa := by sorry
