-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_6_3
-- name    : CutRankSched.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:54:09.739815+00:00
-- url     : https://prove2.me/theorems/dc968ac0-8bc9-4279-a41c-1e71eda0469b
-- title:
--   Theorem 6.3 — connected-exposure treewidth bound
-- statement:
--   Let a valid instance (every exposure subgraph $T_i$ connected) have hardware graph $H$ of treewidth at most $h$. Then the irredundant constraint graph $G_{\mathrm{irr}}=U(D_{\mathrm{cov}})\cup X^\circ$ satisfies
--   $$
--   \mathrm{tw}(G_{\mathrm{irr}}) \le (h+1)(w^\circ+1)(r+1)-1, \tag{14}
--   $$
--   where $w^\circ$ is the vertex-separation width of $X^\circ$ in the given order and $r=\mathrm{rank}_{\mathbb F_2}A$.
--
--   Bounded hardware treewidth, frontier width and rank thus give bounded treewidth for the generic binary-CSP view of the scheduling problem.
--
--   **Formalization Note** Treewidth is the published Prop-valued predicate `RobersonCx.TwLE` ($\mathrm{tw}(G)\le k$).
--
--   Differences from the source:
--   - reading: h = tw(H) → for every h with tw(H) ≤ h; reason: equivalent: the bound is monotone in h and tw(H) itself is such an h
--   - encoding: tw(G) as a number → the Prop tw(G) ≤ k (RobersonCx.TwLE), subtraction in ℕ; reason: same meaning; the product (h+1)(w°+1)(r+1) is at least 1, so no truncation
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 6.3, Eq. (14), p.12

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_width
import Definitions.Def_CutRankSched_Supplement_Girr
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- **Theorem 6.3 (Connected-exposure treewidth bound)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 6.3, Eq. (14), p.12).
Let `h = tw(H)` and suppose every exposure subgraph `T_i` is connected. Then
`tw(G_irr) ≤ (h + 1)(w° + 1)(r + 1) − 1` (14).

**Formalization Note** Treewidth is Prop-valued (the published `RobersonCx.TwLE`); "`h = tw(H)`"
is read as "for every `h` with `tw(H) ≤ h`", equivalent because the bound is monotone in `h`.
Connectedness and support containment come with `Instance.Valid`. The subtraction is in `ℕ`; the
product is at least `1`. -/
theorem theorem_6_3 (I : Instance) (hI : I.Valid) (h : ℕ) (hH : RobersonCx.TwLE I.H h) :
    RobersonCx.TwLE (Girr I) ((h + 1) * (width I + 1) * ((A I).rank + 1) - 1) := by sorry

end Supplement

end CutRankSched
