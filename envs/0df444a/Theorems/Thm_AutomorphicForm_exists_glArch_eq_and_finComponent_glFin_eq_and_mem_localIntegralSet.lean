-- Prove2me | Theorems.Thm_AutomorphicForm_exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet
-- name    : AutomorphicForm.exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/4ab98566-ed2f-5ec4-b35e-9c1c1f77cbd6
-- title:
--   Adelic GL₂ points with prescribed components
-- statement:
--   Let $K$ be a number field (with its ring of integers $\mathcal{O}_K$), let $S$ be a finite set of height-one primes of $\mathcal{O}_K$, let $a \in \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ be an invertible $2\times 2$ matrix over the infinite adele ring of $K$, and let $x$ be an arbitrary family assigning to every height-one prime $v$ an element $x_v \in \mathrm{GL}_2(K_v)$, where $K_v$ is the $v$-adic completion. Then there exists $g \in \mathrm{GL}_2(\mathbb{A}_K)$, over the full adele ring, such that: (i) its archimedean part, the image of $g$ under the group homomorphism induced by the first-coordinate ring homomorphism $\mathbb{A}_K \to \mathbb{A}_{K,\infty}$, equals $a$; (ii) for every $v \in S$, the $v$-component of the finite part of $g$ — that is, the image of $g$ under the second-coordinate homomorphism $\mathbb{A}_K \to \mathbb{A}_K^{\mathrm{fin}}$ followed by evaluation at $v$, applied entrywise — equals $x_v$; and (iii) for every $v \notin S$, that $v$-component lies in [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), i.e. both the matrix of the component and the matrix of its inverse lie in the integral matrix set attached to the valuation ring $\mathcal{O}_v \subseteq K_v$, an entrywise integrality condition.
--
--   This is the surjectivity statement for the component maps of $\mathrm{GL}_2$ over the adeles: any archimedean datum and any finitely many prescribed local data at finite places can be realised simultaneously by a global adelic point, integral at all remaining places. It supports the evaluation of factorisable test functions at spliced adelic points, and is used in the winding-number computation for the hyperbolic terms of the trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : GL (Fin 2) (InfiniteAdeleRing K))
    (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)) :
    ∃ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      AdelicLevel.glArch (𝓞 K) K g = a ∧
      (∀ v ∈ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) = x v) ∧
      ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
        AutomorphicForm.localIntegralSet K v := by sorry
