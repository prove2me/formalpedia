-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom
-- name    : AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/d1028dac-7bcb-51be-99cb-65e7df734190
-- title:
--   Archimedean matching test factors for prime-degree base change
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ whose degree $\operatorname{finrank}_K L$ is prime, let $\sigma$ be a non-trivial $K$-algebra automorphism of $L$, and suppose a $K$-algebra homomorphism $\iota : L \to K_\infty$ into the infinite adele ring of $K$ is given. Let $\mathrm{tys}_L$ be an archimedean type family for $L$, that is, a cardinality $\mathrm{card}(w) \in \mathbb{N}$ for each infinite place $w$ of $L$ together with, for each $i < \mathrm{card}(w)$, a pair consisting of $n \in \mathbb{N}$ and a representation of `rowIsometrySubgroup₀` of the completion at $w$ on $\mathbb{C}^n$. Let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ be such that (i) $\varphi_a$ has compact support and is of the form $g \mapsto \Phi(\mathrm{archEntries}\, g)$ for some $\Phi$ on the space of $2\times 2$ matrices over the mixed space of $L$ that is $C^\infty$ over $\mathbb{R}$, and (ii) $g \mapsto \varphi_a(g^{-1})$ lies in the archimedean cut submodule attached to $\mathrm{tys}_L$ (the intersection over infinite places $w$ of the sums over $i < \mathrm{card}(w)$ of the corresponding type submodules) while $\varphi_a$ lies in the dual cut submodule. Then there exist an archimedean type family $\mathrm{tys}_K$ for $K$ and a function $f_a : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ satisfying the same two conditions over $K$ with respect to $\mathrm{tys}_K$, and matching $\varphi_a$ in the sense of `AreMatchingOn` over $K_\infty$: with $\varphi_a$ transported along `archIdentGL` to $\mathrm{GL}_2(L \otimes_K K_\infty)$ and with the Haar measures `archHaarL`, `archHaarK`, every $\sigma$-twisted orbital integral of $\varphi_a \circ \mathrm{archIdentGL}$ at a $\delta$ with regular semisimple norm string equals every orbital integral of $f_a$ at a regular semisimple $\gamma$ admitting a norm conjugator $y$, for coupled Haar measures on the centraliser of $\gamma$ and on the twisted centraliser of $\delta$; and every orbital integral of $f_a$ at a regular semisimple $\gamma$ which is not a norm vanishes.
--
--   This is the archimedean half of the transfer of test functions for cyclic base change of $\mathrm{GL}_2$ in prime degree, in the case where the hypothesis on $\iota$ forces every archimedean place of $K$ to split completely in $L$; the matching condition is the usual one relating twisted orbital integrals upstairs to orbital integrals downstairs, together with vanishing away from norms. It supplies the archimedean component in the construction of matching test functions of given principal level, used by [`AutomorphicForm.exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three`](thm.html#AutomorphicForm.exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (ι : L →ₐ[K] InfiniteAdeleRing K) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧ AreMatchingArch K L σ φa fa := by sorry
