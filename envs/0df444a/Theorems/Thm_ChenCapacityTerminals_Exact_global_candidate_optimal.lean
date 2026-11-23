-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_global_candidate_optimal
-- name    : ChenCapacityTerminals.Exact.global_candidate_optimal
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T05:55:28.932494+00:00
-- url     : https://prove2.me/theorems/3eadfe9e-97a7-480d-beb6-8c7209892f7e
-- title:
--   Section 4 — optimality of the two-orientation candidate
-- statement:
--   Let $r\in V(G)$. If $X$ minimizes $f$ over nonempty shores excluding $r$, and $Y$ has the same property in $G^{\mathrm{rev}}$, then the cheaper of $X$ and $V(G)\setminus Y$ is a global minimum entering shore of $G$. The proof uses $f_{G^{\mathrm{rev}}}(A)=f_G(V(G)\setminus A)$ and the dichotomy $r\notin Z$ or $r\in Z$ for any global candidate $Z$.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, Theorem 1.1 proof, global-minimum-cut reduction on PDF p.10 (paper p.8): fixed-pair reduction in G and reverse G followed by taking the better cut; Subsection 2.1 for reversal/complement. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.global_candidate_optimal
    (G : Network) (r : ℕ) (hr : r ∈ G.vertices)
    (hG : G.Valid) (X Y : Finset ℕ) (hX : OptimalRoot G r X)
    (hY : OptimalRoot (reverseNetwork G) r Y) :
    OptimalGlobal G (if cut G X ≤ cut G (G.vertices \ Y) then X else G.vertices \ Y) := by sorry
