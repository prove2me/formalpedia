-- Prove2me | Theorems.Thm_AutomorphicForm_exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple
-- name    : AutomorphicForm.exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c88d5865-3014-59f3-a803-5e5d1a99a684
-- title:
--   Compact open kernel in the centraliser of a regular semisimple γ
-- statement:
--   Let $K$ be a number field, let $v$ be a height one prime of the ring of integers $\mathcal{O}_K$, with $K_v$ the associated adic completion of $K$, and let $\gamma$ be an element of $\mathrm{GL}_2(K_v)$. Assume that $\gamma$ is regular semisimple in the sense used throughout the development, namely that the discriminant $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ of its characteristic polynomial, computed from the underlying $2\times 2$ matrix, is a unit of $K_v$ (equivalently, since $K_v$ is a field, nonzero). Write $T_\gamma$ for the local centraliser of $\gamma$, i.e. the subgroup $\mathrm{Centralizer}\,\{\gamma\}$ of $\mathrm{GL}_2(K_v)$ consisting of those elements commuting with $\gamma$, carrying the subspace topology. The assertion is that there exists a monoid homomorphism $\chi \colon T_\gamma \to \mathbb{Z}^2$, the target being $\mathrm{Fin}\,2 \to \mathbb{Z}$ written multiplicatively, such that the image of $\ker \chi$ under the inclusion $T_\gamma \hookrightarrow \mathrm{GL}_2(K_v)$ is a compact subset of $\mathrm{GL}_2(K_v)$, and such that $\ker\chi$ is an open subset of $T_\gamma$.
--
--   This is the standard structural fact about Cartan subgroups of $\mathrm{GL}_2$ over a nonarchimedean local field used in the theory of orbital integrals: the centraliser of a regular semisimple element is the unit group of a two-dimensional commutative $K_v$-algebra, and modulo a free quotient of rank at most two it is compact. It is used here to produce the compact set of the orbital estimate recorded in [`AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul`](thm.html#AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    ∃ χ : AutomorphicForm.localCentralizer K v γ →* Multiplicative (Fin 2 → ℤ),
      IsCompact (Subtype.val '' (χ.ker : Set (AutomorphicForm.localCentralizer K v γ))) ∧
        IsOpen (χ.ker : Set (AutomorphicForm.localCentralizer K v γ)) := by sorry
