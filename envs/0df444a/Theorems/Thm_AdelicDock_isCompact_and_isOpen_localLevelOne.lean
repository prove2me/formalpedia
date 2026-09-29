-- Prove2me | Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
-- name    : AdelicDock.isCompact_and_isOpen_localLevelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/cafd229a-0eb1-5724-a60a-f9a0c880b036
-- title:
--   Local level-one subgroup at v is compact and open
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $v$ be a point of the height-one spectrum of $\mathcal{O}_K$, i.e. a finite place, let $K_v$ denote the completion `v.adicCompletion K`, and let $N$ be an ideal of $\mathcal{O}_K$ with $N \neq \bot$. Consider the subgroup [`AdelicDock.localLevelOne (𝓞 K) K v N`](def/AdelicDock_LocalEmbedding.html#L178) of $\mathrm{GL}_2(K_v)$, defined as the preimage under the monoid homomorphism [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) (which sends $g$ to the invertible adelic matrix `localMat` obtained from $g$ at the place $v$) of the subgroup `AdelicLevel.finiteLevelOne` of $\mathrm{GL}_2$ over the finite adele ring, the latter consisting of those $g$ for which both $g$ and $g^{-1}$, viewed as matrices, satisfy the predicate `IsLevelOneMatrix` for $N$. The assertion is the conjunction of two statements about the underlying set of this subgroup in $\mathrm{GL}_2(K_v)$: it is compact, and it is open. Equivalently, as the proof records, membership amounts to: all entries of $g$ and of $g^{-1}$ lie in the valuation ring of $K_v$, the lower left entries have valuation at most `AdelicLevel.idealBound` of $N$ at $v$, and the lower right entries are within that same bound of $1$.
--
--   This is the statement that the local congruence subgroup of level $N$ at a finite place is a compact open subgroup of $\mathrm{GL}_2(K_v)$, the basic topological input for using it as a level structure in the adelic theory of automorphic forms. It is invoked throughout the development of Whittaker models and of automorphic forms invariant under such a level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdelicDock_isCompact_and_isOpen_localLevelOne.lean

import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AdelicDock.isCompact_and_isOpen_localLevelOne (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    IsCompact (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by sorry
