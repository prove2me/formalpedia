-- Prove2me | Theorems.Thm_AutomorphicForm_adelicHeight_sigmaAdelicAct
-- name    : AutomorphicForm.adelicHeight_sigmaAdelicAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/f08cc8f3-83a0-5824-a775-30ce9957a6dc
-- title:
--   Galois invariance of the adelic height on GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $D$ be an idèle Galois descent datum for $\mathcal{O}_L$ over the extension $L/K$: a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adèle ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, such that each $D.\mathrm{act}\,\sigma$ is continuous and agrees with $\sigma$ on principal adèles, i.e. $D.\mathrm{act}\,\sigma\,(\iota x) = \iota(\sigma x)$ for all $x \in L$, where $\iota$ is the structure map $L \to \mathbb{A}_L$. Fix such a $\sigma$ and an element $g$ of $\mathrm{GL}_2(\mathbb{A}_L)$. The twist `sigmaAdelicAct K L D σ` is the group homomorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying the ring automorphism $D.\mathrm{act}\,\sigma$ entrywise. The assertion is that the adelic height of $L$ is unchanged by this twist: $\mathrm{adelicHeight}\,(\sigma_{\mathbb{A}} g) = \mathrm{adelicHeight}\,g$, where the adelic height of an element of $\mathrm{GL}_2(\mathbb{A}_L)$ is the product of the archimedean height of its infinite part, namely $\prod_{w \mid \infty} \mathrm{localHeight}(g_w)^{\,\mathrm{mult}(w)}$ over the infinite places of $L$, with the finite height of its finite part, namely the finitely supported product $\prod_{\mathfrak{p}} \mathrm{finLocalHeight}(g_{\mathfrak{p}})$ over the height-one primes of $\mathcal{O}_L$.
--
--   This is the statement that the height function entering the truncation of automorphic forms on $\mathrm{GL}_2$ over a number field is invariant under the Galois twist coming from an idèle descent datum: $\sigma$ permutes the places of $L$ over a given place of $K$, and the local heights and local degrees at $w$ and $\sigma \cdot w$ agree. It is used where truncation has to commute with the twist, and is cited by [`AutomorphicForm.constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn`](thm.html#AutomorphicForm.constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn) and by the existence statement for integrable truncated products attached to `sigmaAdelicAct`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adelicHeight_sigmaAdelicAct.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.adelicHeight_sigmaAdelicAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.sigmaAdelicAct K L D σ g) =
      NumberField.AdelicHeight.adelicHeight L g := by sorry
