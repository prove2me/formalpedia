-- Prove2me | Theorems.Thm_CookPvsNP_mem_NP_of_polyReducible
-- name    : CookPvsNP.mem_NP_of_polyReducible
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T01:01:25.68089+00:00
-- url     : https://prove2.me/theorems/a573db96-7882-40d1-ba71-051dac13412b
-- title:
--   NP is closed under polynomial-time many-one reductions
-- statement:
--   Let $\Sigma_1,\Sigma_2$ be finite alphabets and let $L_1\subseteq\Sigma_1^*$, $L_2\subseteq\Sigma_2^*$ be languages. If $L_1\le_p L_2$ (polynomial-time many-one reducibility, Cook's Definition 3) and $L_2\in\mathrm{NP}$, then
--   $$L_1\in\mathrm{NP}.$$
--
--   This is the standard closure of NP under polynomial-time reductions. Applied to complements (a reduction $f$ from $L_1$ to $L_2$ is also a reduction from $L_1^{c}$ to $L_2^{c}$) it shows that co-NP is closed under polynomial-time reductions as well; for instance, if an NP-complete language lies in co-NP then NP $=$ co-NP.
--
--   **Formalization Note** P, NP and $\le_p$ are those of the Cook problem description (one-tape Turing machines, time bound $|w|^k+k$, checking relations with certificates of length at most $|w|^k$).
-- source:
--   S. Cook, The P versus NP problem (Clay Mathematics Institute problem description), §2, remarks after Definition 4 (closure of NP under ≤p); used in Karp & Papadimitriou, MIT/LCS/TM-154 (1980), p. 8, proof of Corollary 1

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

theorem mem_NP_of_polyReducible {Sym₁ Sym₂ : Type} [Fintype Sym₁] [Fintype Sym₂]
    (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) (hred : PolyReducible L₁ L₂) (h₂ : L₂ ∈ NP Sym₂) :
    L₁ ∈ NP Sym₁ := by sorry

end CookPvsNP
