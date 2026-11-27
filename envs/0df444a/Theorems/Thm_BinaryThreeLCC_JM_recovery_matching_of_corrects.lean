-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_recovery_matching_of_corrects
-- name    : BinaryThreeLCC.JM.recovery_matching_of_corrects
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:03:11.062724+00:00
-- url     : https://prove2.me/theorems/7fa65ce9-ac2d-4ca3-9f96-681a69edfed9
-- title:
--   Recovery matching for one nonzero coordinate of a 3-query linear LCC (Fact 2.1)
-- statement:
--   Let $C:\mathbb F_2^k\to\mathbb F_2^n$ be an injective linear code with an operational corrector: for every requested position $u\in[n]$, a probability distribution over binary oracle decision trees of depth at most $3$. Suppose that for real numbers $\delta$ and $\varepsilon<1/2$ the corrector succeeds, i.e. for every message $b$, every received word $y$ with $\Delta(y,C(b))\le\delta n$ and every $u$, the output equals $C(b)_u$ with probability at least $1-\varepsilon$.
--
--   Let $v_1,\dots,v_{2n}$ be the padded rows of $C$ ($v_u$ is the $u$-th row for $u\le n$ and $v_u=0$ otherwise). Fix $u\in[n]$ with $v_u\neq0$. Then there is a family $\mathcal H_u$ of $3$-element subsets of $[2n]\setminus\{u\}$, pairwise disjoint, such that
--
--   $$3\,|\mathcal H_u|+1>\delta n\qquad\text{and}\qquad v_u=v_a+v_b+v_c\ \text{ for every }\{a,b,c\}\in\mathcal H_u .$$
--
--   In particular $|\mathcal H_u|\ge\lfloor\delta n\rfloor/3$. This is the combinatorial form of a linear $3$-LCC (Fact 2.1 of the source), stated for a single target with nonzero row; the corruption budget is the integer one forced by the Hamming-ball condition.
--
--   **Formalization Note** Decision trees are `MantriCVQ.DT` restricted to depth at most $3$, and success probabilities are computed from a `PMF` over trees, exactly as in the mission's `CodeModel`.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Fact 2.1 (printed pp. 2–3), citing Kothari–Manohar STOC 2024 Def. 2.3 / Fact 2.4

import Definitions.Def_BinaryThreeLCC_Main_Matchings

set_option autoImplicit false

namespace BinaryThreeLCC.JM

open BinaryThreeLCC.Main

theorem recovery_matching_of_corrects {k n : ℕ} (C : CodeModel k n) (δ ε : ℝ)
    (hε1 : ε < 1 / 2) (hcorrect : Corrects C δ ε) (u : Fin n) (hu : codeRow C u ≠ 0) :
    ∃ H : Finset (Finset (Fin (2 * n))),
      IsRecoveryMatching (⟨u.val, by omega⟩ : Fin (2 * n)) H ∧
      δ * n < 3 * (H.card : ℝ) + 1 ∧
      ∀ e ∈ H, paddedRow C ⟨u.val, by omega⟩ = ∑ a ∈ e, paddedRow C a := by sorry

end BinaryThreeLCC.JM
