-- Prove2me | Theorems.Thm_DLevelNestedLogit_Assortment_root_local_iff_optimal
-- name    : DLevelNestedLogit.Assortment.root_local_iff_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:01:48.233823+00:00
-- url     : https://prove2.me/theorems/6349fc5f-733c-4c88-b36e-54f9ed575450
-- title:
--   §4 (p. 329): the local problem at root is identical to the assortment problem (3)
-- statement:
--   Consider a $d$-level nested logit model with $\eta_{\mathrm{root}}=0$, $\eta_j\in(0,1]$ at the other nonleaf nodes, and $v_0,\dots,v_n>0$, and let $t^*$ be the scalars computed from an assortment $S^*$. Because $V_{\mathrm{root}}(S_{\mathrm{root}})=1$ and $t^*_{\mathrm{Parent}(\mathrm{root})}=0$, the objective of the local problem at the root is the expected revenue:
--   $$V_{\mathrm{root}}(S_{\mathrm{root}})\big(R_{\mathrm{root}}(S_{\mathrm{root}})-t^*_{\mathrm{Parent}(\mathrm{root})}\big)=R_{\mathrm{root}}(S_{\mathrm{root}})\quad\text{for every }S,$$
--   and a set $S$ is an optimal solution of the local problem at root if and only if it is an optimal solution of the assortment problem (3).
--
--   This is the observation that lets the corollary on revenue thresholds conclude from the local problems: whatever solves the local problem at the root solves (3).
--
--   **Formalization Note.** The statement has three conjuncts: `tparent … root = 0`, the identity of objectives for every finset `S'`, and the equivalence of `IsLocalOptimal` at the root with `IsOptimalAssortment`. It holds for the scalars computed from any `Sstar`, since the root's threshold is the convention `0`. The equivalence uses $N_{\mathrm{root}}=\{0,1,\dots,n\}$.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 329, §4, left column, paragraph after (4)

import Mathlib
import Definitions.Def_DLevelNestedLogit_Assortment_Tree
import Definitions.Def_DLevelNestedLogit_Assortment_Choice

namespace DLevelNestedLogit.Assortment

open ProductTree

theorem root_local_iff_optimal (n : ℕ) (T : ProductTree n) (η : T.Node → ℝ)
    (v r : Fin (n + 1) → ℝ) (hη : T.StandingEta η) (hv : ∀ i, 0 < v i)
    (Sstar S : Finset (Fin (n + 1))) :
    T.tparent η v r Sstar T.root = 0 ∧
    (∀ S', T.localObj η v r T.root (T.tparent η v r Sstar T.root) S' = T.R η v r S' T.root) ∧
    (T.IsLocalOptimal η v r T.root (T.tparent η v r Sstar T.root) S ↔
      T.IsOptimalAssortment η v r S) := by sorry

end DLevelNestedLogit.Assortment
