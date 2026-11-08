-- Prove2me | Theorems.Thm_AvoidPlast_item1_imp_item3
-- name    : AvoidPlast.item1_imp_item3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:24.921923+00:00
-- url     : https://prove2.me/theorems/27b6dc8e-708f-418f-9af6-89a071c67a6d
-- title:
--   Proof of Theorem 5.14, (1)⇒(3): low-space simulation of FP implies hardness of Diag$_\varepsilon$
-- statement:
--   Item (1) of Theorem 5.14 implies Item (3): if every $f\in\mathrm{FP}$ has for every $\gamma>0$ a deterministic space-$n^\gamma$ machine correct on a $1-n^{-\omega(1)}$ fraction of inputs, then for every $\varepsilon\in(0,1)$ and every polynomial-time $B$, $\Pr_x[B(x)\in\mathrm{Diag}_\varepsilon(x)]\le n^{-\omega(1)}$. No derandomization hypothesis is needed.
--
--   Differences from the source:
--   - encoding: $n^{-\omega(1)}$ → an existential negligible $\nu$ (the published `QuantumPRC.Negligible`: for every real $c>0$, eventually $|\nu(n)|<n^{-c}$); reason: the standard meaning; reading R1 of the paper notes
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
--   - reading: fix a universal deterministic machine $U_\varepsilon$ with budgets $n^{\varepsilon^2}$ work space and $2^{n^{\varepsilon^2}}$ steps → the function $U_\varepsilon$ denoted by it: descriptions $0^j1e$, budgets $\lceil n^{\varepsilon^2}\rceil$ bits of simulation size and $2^{\lceil n^{\varepsilon^2}\rceil}$ steps; reason: the page leaves the universal machine open; the proof uses only universality and low-space evaluability, and the bit budget is what makes both true; reading R4
--   - reading: the machine model is the RAM model (p.13), unspecified → a multitape machine with read-only input tapes, each accessed by head moves and index jumps, a fixed work alphabet and a write-only output; reason: the page does not fix a RAM; FP and space $n^\gamma$ are robust under the choice, and sublinear time needs the random access; reading R5
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (1)⇒(3), p.29

import Mathlib
import Definitions.Def_AvoidPlast_LowSpaceFP
import Definitions.Def_AvoidPlast_DiagHard

namespace AvoidPlast

/-- Item (1) implies Item (3) (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (1)⇒(3), p.29). No derandomization
hypothesis is needed. -/
theorem item1_imp_item3 : LowSpaceFP → DiagHard := by sorry

end AvoidPlast
