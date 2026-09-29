-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/2c67387d-91c6-5161-97fd-a8213956ff83
-- title:
--   A σ-stable enlargement of an archimedean type family
-- statement:
--   Let $K$ be a field and $L$ a number field which is a $K$-algebra, let $D$ be an idèle Galois descent datum for $\mathcal{O}_L$ over $K$ in $L$ — that is, a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adele ring $\mathbb{A}_L$, each continuous and compatible with the structure map $L \to \mathbb{A}_L$ in the sense that $D.\mathrm{act}\,\sigma$ restricted to $L$ is $\sigma$ — let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\mathrm{tys}$ be an archimedean type family for $L$, i.e. a natural number $\mathrm{card}\,w$ for each infinite place $w$ of $L$ together with, for each $i < \mathrm{card}\,w$, a pair consisting of an $n$ and a complex representation of `rowIsometrySubgroup₀` of the completion $L_w$ on $\mathbb{C}^n$. Then there is an archimedean type family $\mathrm{tys}'$ such that (i) for every infinite place $w$ and every index $i$ of $\mathrm{tys}$ at $w$ there is an index $j$ of $\mathrm{tys}'$ at $w$ with $\mathrm{tys}'.\mathrm{rep}\,w\,j = \mathrm{tys}.\mathrm{rep}\,w\,i$, and (ii) the submodule $\bigcap_w \sum_{i} \mathrm{archTypeSubmoduleAt}\,L\,w\,(\mathrm{tys}'.\mathrm{rep}\,w\,i)$ of complex-valued functions on $\mathrm{GL}_2(\mathbb{A}_L)$ is carried into itself by $u \mapsto u \circ \mathrm{GL}_2(D.\mathrm{act}\,\sigma)$.
--
--   This is the saturation step for archimedean $K$-types under a Galois twist: the automorphism $\sigma$ permutes the infinite places of $L$ and transports types along the resulting orbits, so any finite family of types can be enlarged to one whose archimedean cut is stable under the twist. It is used in the construction of a nonvanishing twisted cut trace, via [`AutomorphicForm.exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers`](thm.html#AutomorphicForm.exists_twistedCutTrace_ne_zero_of_pos_of_isArithGenuineCuspRealizable_of_isConstantOnFibers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_isContainedIn_forall_sigmaSectionActOn_mem_archCutSubmodule
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (tys : ArchTypeFamily L) :
    ∃ tys' : ArchTypeFamily L, ArchTypeFamily.IsContainedIn L tys tys' ∧
      ∀ u ∈ archCutSubmodule L tys', sigmaSectionActOn K L D σ u ∈ archCutSubmodule L tys' := by sorry
