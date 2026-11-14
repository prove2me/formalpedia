-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_ksRun_phase
-- name    : BCFGJPSSV26.Stable.ksRun_phase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:43:36.479534+00:00
-- url     : https://prove2.me/theorems/7712e81b-f789-4a1b-aa97-23b238077f53
-- title:
--   Cluster sampling (Part II, Algorithm 2) — every run is done within $20s+20$ steps
-- statement:
--   Termination of the cluster sampling of Part II (arXiv:2610.17172), Algorithm 2, in the form in which the formalization runs it: a state machine that reads one chunk of coins per step is in its final phase after $20s+20$ steps, whatever the chunks.
--
--   **The state machine.** The parameters are natural numbers $N,s,b$, the data $(n,m,k,\text{table of distances})$ of an instance, a list $LS$ of facility indices (the local-search centers) and a list $\Lambda_1$ of dummies (the outcome of the client sampling). A state consists of a phase $\phi$ ($0$, $1$, or $2$ when done), a counter $j$ of outer iterations, the list $R^-$ of deleted centers, the list $\Lambda_2$ of dummies, and a mode with a current center $\ell$ and a radius base $r_0$. The initial state has $\phi=0$, $j=0$, empty lists and mode START. A step reads a number $u$; write $LS'=LS\setminus R^-$ and "bit" for $[\,2u<2^b\,]$. In phase $2$ nothing changes; otherwise:
--
--   - START: if $j=s$, go to the next phase (from $0$ to $1$, otherwise to $2$) with $j=0$; else on bit $1$ end the iteration, on bit $0$ go to SAMPLE.
--   - SAMPLE: if $LS'$ is empty end the iteration; else draw $\ell\in LS'$ by a weighted sample from $u$ (weights: the cost of the local-search cluster in phase $0$, the cost of the cluster in the mixed set $(LS',\Lambda_1\cup\Lambda_2)$ otherwise) and go to RADD.
--   - RADD: if $|R^-|\le s$ and the bit is $1$, delete $\ell$ and end the iteration; else go to DG.
--   - DG: if $|\Lambda_2|+|R^-|>2s$, or no center other than $\ell$ is kept, end the iteration; else, with $c'$ the kept center other than $\ell$ nearest to $\ell$: on bit $1$ go to RG with $r_0=d(\ell,c')$, on bit $0$ delete $c'$ and stay in DG.
--   - RG: if $|\Lambda_2|+|R^-|>2s$, delete $\ell$ and end the iteration; else append the dummy with leader $\ell$ and radius $r_0N^{-3}\bigl(\tfrac{N+1}{N}\bigr)^{x}+|\Lambda_2|\,r_0/(N^4(2s+2))$, $x=u\bmod(10N^2+1)$, and go to RGB.
--   - RGB: on bit $1$ delete $\ell$ and end the iteration; on bit $0$ go back to RG.
--
--   Ending an iteration means $j\leftarrow j+1$ and mode START.
--
--   **Statement.** For all parameters $N,s,b$, all instance data, all lists $LS$ and $\Lambda_1$, and every sequence of chunks $u_0,u_1,\dots$, the state reached from the initial state after the $20s+20$ steps reading $u_0,\dots,u_{20s+19}$ satisfies
--   $$\phi=2 .$$
--
--   No assumption is made on the instance data or on the lists. The result is used in the process lemma of the cluster sampling: the run always ends in phase $2$, where the invariant of the analysis yields a good outcome; it is also what bounds the number of chunks ($20s+20$) that the cluster sampling reads in each trial.
--
--   **Formalization Note** The algorithm of the paper is a nested loop; here each elementary random choice is one step, and the guards $|R^-|\le s$ and $|\Lambda_2|+|R^-|\le 2s$ bound the deletions and additions on every input. The radius of the $t$-th dummy is shifted by $t\,r_0/(N^4(2s+2))$ so that the dummies of one leader are distinct.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Algorithm 2. Lean source: `BCFGJPSSV26.Stable.ksRun_phase`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSampling.lean#L210-L224

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

namespace KSState

end KSState

namespace KSSteps

end KSSteps

theorem ksRun_phase (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (ch : ℕ → ℕ) : (ksRun N x LS Λ₁ s b ch).phase = 2 := by sorry

end BCFGJPSSV26.Stable
end
