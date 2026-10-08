-- Prove2me | Theorems.Thm_FixpNash_WeakApprox_isEpsApproxNash_iff_pure
-- name    : FixpNash.WeakApprox.isEpsApproxNash_iff_pure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:32.706719+00:00
-- url     : https://prove2.me/theorems/d4de883c-690f-47a9-933a-33755be530f9
-- title:
--   p. 12 — for an ε-NE it is sufficient to check switches to pure strategies
-- statement:
--   Let $\Gamma$ be a finite game with players $i$, finite pure-strategy sets $S_i$ and real payoffs $u_i$, let $x$ be a real vector indexed by the pairs $(i,j)$ with $j\in S_i$, and let $\varepsilon$ be a real number. Recall that $x$ is an **$\varepsilon$-Nash equilibrium** ($\varepsilon$-NE) if $x$ is a mixed profile and for every player $i$ and every mixed strategy $y_i$ of $i$, $u_i(x)\ge u_i(y_i;x_{-i})-\varepsilon$. Then $x$ is an $\varepsilon$-NE if and only if $x$ is a mixed profile and
--   $$u_i((i{:}j);x_{-i})\le u_i(x)+\varepsilon\qquad\text{for every player } i \text{ and every } j\in S_i,$$
--   that is, $g_{i,j}(x)\le\varepsilon$ for all $i,j$.
--
--   The paper states this in parentheses where it defines $\varepsilon$-NE ("again, it is sufficient to check switches to pure strategies only"). Both directions of Proposition 3 use it: the first to read off $g_{i,j}(x)\le\varepsilon$ from an $\varepsilon$-NE, the second to conclude an $\varepsilon$-NE from $\max\{0,g_{i,j}(x)\}\le\varepsilon$.
--
--   **Formalization Note** The $\varepsilon$-NE is the published `DGPNash.WellSupported.IsEpsApproxNash` and $u_i((i{:}j);x_{-i})$ the published `DGPNash.NashMap.purePayoff`. The statement is made for every real $\varepsilon$; the paper uses it for $\varepsilon>0$.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), §2.2, p. 12 (definition of ϵ-NE, parenthetical remark)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace FixpNash.WeakApprox

/-- p. 12: for an ε-NE "it is sufficient to check switches to pure strategies only". -/
theorem isEpsApproxNash_iff_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) :
    DGPNash.WellSupported.IsEpsApproxNash u x ε ↔
      AGT.IsMixedProfile x ∧
        ∀ (i : ι) (j : S i),
          DGPNash.NashMap.purePayoff u x i j ≤ AGT.expectedPayoff u x i + ε := by sorry

end FixpNash.WeakApprox
