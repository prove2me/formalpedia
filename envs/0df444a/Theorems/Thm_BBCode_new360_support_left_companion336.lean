-- Prove2me | Theorems.Thm_BBCode_new360_support_left_companion336
-- name    : BBCode.new360_support_left_companion336
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T15:34:22.32582+00:00
-- url     : https://prove2.me/theorems/6148b667-279a-48eb-8435-92bfbd21226d
-- title:
--   360-qubit new: stabilizer extraction, left companion336
-- statement:
--   For the new bivariate-bicycle code on $G=\mathbb Z_6\times\mathbb Z_{30}$ with $A=1+y+xy^2$ and $B=1+y^8+x^2y^{16}$, let $v$ have zero $H_X$ syndrome and weight at most ten. Suppose its left coordinate $(0,0)$ is nonzero and at least one of right coordinate $(5,6)$ is nonzero. There is a Z-stabilizer $u$ supported inside $v$ which contains the anchor:
--
--   $$H_Xu=0,\quad u\in\operatorname{row}(H_Z),\quad u_{\rm anchor}=1,\quad\operatorname{supp}(u)\subseteq\operatorname{supp}(v).$$
--
--   This support-extraction statement is a hypothesis used in the small-kernel reduction for this specific code. Its conclusion concerns a stabilizer supported inside the given vector.
-- source:
--   Auxiliary anchored support-extraction case genuinely used in the reduction of existing captain milestone BBCode.new360_params, https://prove2.me/theorems/5cfa9063-07f8-4665-9813-ea43082ce94a. Captain citation: Daugherty–Ryan–Ward (2026), Table 3 p.5, Table 9 p.15; the exact external preprint was not independently located. General distance/sector convention: Bravyi et al., https://arxiv.org/html/2308.07915v2#S4, Section 4 Lemma 1.

import Definitions.Def_BBCode_Setting
open Matrix

theorem BBCode.new360_support_left_companion336 (v : BBCode.Qubit 6 30 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inl (0,0)) ≠ 0)
    (hb : v (Sum.inr (5,6)) ≠ 0) :
    ∃ u : BBCode.Qubit 6 30 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)}) ∧
      u (Sum.inl (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := by sorry
