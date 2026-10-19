-- Prove2me | Theorems.Thm_BBCode_new336_class2_support_right_companion194
-- name    : BBCode.new336_class2_support_right_companion194
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T14:42:05.244931+00:00
-- url     : https://prove2.me/theorems/b73fcde4-82e2-49b9-bad8-0722872c23e7
-- title:
--   336-qubit class 2: stabilizer extraction, right companion194
-- statement:
--   For the class-2 bivariate-bicycle code on $G=\mathbb Z_2\times\mathbb Z_{84}$ with $A=1+y+xy^5$ and $B=1+y^{20}+y^{46}$, let $v$ have zero $H_X$ syndrome and weight at most ten. Suppose its right coordinate $(0,0)$ is nonzero and at least one of right coordinate $(0,26)$ is nonzero. There is a Z-stabilizer $u$ supported inside $v$ which contains the anchor:
--
--   $$H_Xu=0,\quad u\in\operatorname{row}(H_Z),\quad u_{\rm anchor}=1,\quad\operatorname{supp}(u)\subseteq\operatorname{supp}(v).$$
--
--   This support-extraction statement is a hypothesis used in the small-kernel reduction for this specific code. Its conclusion concerns a stabilizer supported inside the given vector.
-- source:
--   Auxiliary anchored support-extraction case genuinely used in the reduction of existing captain milestone BBCode.new336_class2_params, https://prove2.me/theorems/c1c39db9-186d-4fcc-8fd4-0507b8f1f0d0. Captain citation: Daugherty–Ryan–Ward (2026), Table 3 p.5, Table 9 p.15; the exact external preprint was not independently located. General distance/sector convention: Bravyi et al., https://arxiv.org/html/2308.07915v2#S4, Section 4 Lemma 1.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.new336_class2_support_right_companion194 (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0,0)) ≠ 0)
    (hb : v (Sum.inr (0,26)) ≠ 0) :
    ∃ u : BBCode.Qubit 2 84 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,5)} {(0,0),(0,20),(0,46)}) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := by sorry
