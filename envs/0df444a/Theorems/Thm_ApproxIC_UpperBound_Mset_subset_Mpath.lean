-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_Mset_subset_Mpath
-- name    : ApproxIC.UpperBound.Mset_subset_Mpath
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:21.731314+00:00
-- url     : https://prove2.me/theorems/aeb788af-3cda-4d81-90e7-b7b53548538a
-- title:
--   §3.2.1, p. 17 — every ε-IC, IR mechanism is feasible for the path relaxation: M(ε) ⊆ M_path(ε)
-- statement:
--   Let $f$ be a value density on $S=[0,\bar v]$ and fix a path $(\mu,\nu_0,v^\star,w)$ with $0<\mu<\nu_0<\bar v$ and $v^\star:[\mu,\bar v]\to[0,\nu_0]$. For every $\varepsilon$,
--   $$\mathcal M(\varepsilon)\subseteq\mathcal M_{\text{path}}(\varepsilon).$$
--   That is, a mechanism satisfying (IR) on all of $S$ and (IC$_\varepsilon$) for all pairs of types satisfies (IR$_\mu$) on $[0,\mu]$ and (IC$_\mu$) along the path $v\mapsto v^\star(v)$.
--
--   Consequently $\Pi^\star(\mathcal M(\varepsilon))\le\Pi^\star(\mathcal M_{\text{path}}(\varepsilon))$, the first step of the upper bound.
--
--   **Formalization Note** The page's "Clearly, $\Pi^\star(\mathcal M(\varepsilon))\le\Pi^\star(\mathcal M_{\text{path}}(\varepsilon))$" is stated as the set inclusion behind it; combined with the $\forall$-form of Lemma 1 it yields the inequality of suprema without forming $\Pi^\star(\mathcal M_{\text{path}}(\varepsilon))$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 17, §3.2.1, (P_path), sentence after (IC_µ)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

namespace ApproxIC.UpperBound

theorem Mset_subset_Mpath (M : Model) (P : Path M) (ε : ℝ) :
    Mset M ε ⊆ MpathSet M P ε := by sorry

end ApproxIC.UpperBound
