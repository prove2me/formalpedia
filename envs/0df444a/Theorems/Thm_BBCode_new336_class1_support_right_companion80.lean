-- Prove2me | Theorems.Thm_BBCode_new336_class1_support_right_companion80
-- name    : BBCode.new336_class1_support_right_companion80
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T13:43:14.604855+00:00
-- url     : https://prove2.me/theorems/38857fc8-7f37-4d77-8f54-1e95d2510f48
-- title:
--   336-qubit class 1: stabilizer extraction, right companion80
-- statement:
--   For the class-1 bivariate-bicycle code on $G=\mathbb Z_2\times\mathbb Z_{84}$ with $A=1+y+xy^5$ and $B=1+y^4+y^{62}$, let $v$ have zero $H_X$ syndrome and weight at most ten. Suppose its right coordinate $(0,0)$ is nonzero and at least one of left coordinate $(0,80)$ is nonzero. There is a Z-stabilizer $u$ supported inside $v$ which contains the anchor:
--
--   $$H_Xu=0,\quad u\in\operatorname{row}(H_Z),\quad u_{\rm anchor}=1,\quad\operatorname{supp}(u)\subseteq\operatorname{supp}(v).$$
--
--   This is a support-extraction subcase used in the reduction of the existing small-kernel theorem. The five possible companions arise from a single odd check row and are treated individually at each origin. Translation and strict induction on support size complete the reduction.
-- source:
--   Auxiliary anchored support-extraction case for existing BBCode.new336_class1_small_kernel, https://prove2.me/theorems/5ddbc879-5c73-4792-ab0f-b94ff6acb8e7. Original parameters: Daugherty–Ryan–Ward (2026), Table 3 p.5, Table 9 p.15. General distance/sector convention: Bravyi et al., https://arxiv.org/html/2308.07915v2#S4, Section 4 Lemma 1.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.new336_class1_support_right_companion80 (v : BBCode.Qubit 2 84 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0,0)) ≠ 0)
    (hb : v (Sum.inl (0,80)) ≠ 0) :
    ∃ u : BBCode.Qubit 2 84 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,5)} {(0,0),(0,4),(0,62)}) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := by sorry
