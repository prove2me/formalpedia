-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_theorem_1
-- name    : AggregatedCodeTesting.Testing.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:15.766538+00:00
-- url     : https://prove2.me/theorems/d5cfb696-75ed-4d50-9b82-8293c29b3582
-- title:
--   Theorem 1 — exact identifiability: equal laws iff equal block-coset profiles
-- statement:
--   Let $C\le\mathbb F_2^m$ be any binary linear code and $w\ge1$. For offset sequences $\ell,\ell'\in(\mathbb F_2^m)^w$, let $P_\ell$ and $P_{\ell'}$ be the laws of the aggregate observation $H_e=\sum_{j=1}^w(\ell_j+U_j)_e$ with independent uniform masks $U_j\in C$, and let $T_C(\ell)$ be the block-coset profile. Then
--
--   $$
--   P_\ell=P_{\ell'}\iff T_C(\ell)=T_C(\ell').
--   $$
--
--   The observation law therefore identifies exactly the coset counts on the indecomposable coordinate blocks, and nothing more: the lane order and the alignment of lanes across blocks are invisible. The theorem holds for every code, including codes with identically zero coordinates (whose singleton blocks carry deterministic counts).
--
--   Differences from the source:
--   - encoding: the coset counts $n_{D,\sigma}$ indexed by $\sigma\in Q_D$ → counts indexed by a representative $x\in\mathbb F_2^m$ of $\sigma$; reason: every coset has representatives, and equality of the families is the same condition.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 1, printed p. 3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Model

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Theorem 1 (Exact identifiability), printed p. 3 (PDF p. 4): for every binary linear code
`C ≤ F₂^m` and width `w ≥ 1`, the observation laws of `ℓ` and `ℓ′` coincide iff their
block-coset profiles coincide. -/
theorem theorem_1 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (w : ℕ) (hw : 0 < w)
    (ℓ ℓ' : Fin w → Word m) :
    law C ℓ = law C ℓ' ↔ profile C ℓ = profile C ℓ' := by sorry

end AggregatedCodeTesting.Testing
