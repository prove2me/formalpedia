-- Prove2me | Theorems.Thm_ConsistentSubmodular_uniformRoundedFamilies
-- name    : ConsistentSubmodular.uniformRoundedFamilies
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:43.164076+00:00
-- url     : https://prove2.me/theorems/a22b8a87-96d6-4167-b046-62a7a8350278
-- title:
--   Uniform rounded window and bridge families from certificates
-- statement:
--   Let $O$ be a certificate family (level $\alpha=O.\mathrm{level}\in[0,3/4]$ and positive segment budgets $O.\mathrm{budget}(m)$ for windows with last stage $m$), and let $N\ge200$. Put $S=O.\mathrm{budget}(3N+1)$, $H=\texttt{familyHeavy}\ N\ S=\texttt{windowHeavyBound}\ N\ S+\texttt{bridgeHeavy}\ N$ and $L=\texttt{familyLength}\ S=100S+20$. Then the uniform rounded-families property holds at level $\alpha$ with parameters $(N,H,L)$: for all $n,k$, every objective $f$ on $[n]$ and every transfer parameter system $p$ for $(N,H,k)$ there is a rounded window family for $(f,p.\mathrm{core},\alpha-2/N,\texttt{transferClock}\,f\,p,\;p.\mathrm{core}+p.\mathrm{block}+H,\;L)$ together with a rounded bridge family for it.
--
--   The constants $H$ and $L$ depend only on $N$ and on the certificate budget, not on the instance or the level. Endpoint-preserving local families thus supply the rounded windows and bridges of the schedule at the level of the certificates.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/UniformRoundedFamilies.lean#L23-L66 (`ConsistentSubmodular.uniformRoundedFamilies`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformRoundedFamilies

open ConsistentSubmodular

theorem ConsistentSubmodular.uniformRoundedFamilies (O : CertificateFamily) (N : ℕ) (hN : 200 ≤ N) :
    HasUniformRoundedFamilies O.level N (familyHeavy N (O.budget (3 * N + 1)))
      (familyLength (O.budget (3 * N + 1))) := by sorry
