-- Prove2me | Theorems.Thm_AvoidPlast_item3_imp_item2
-- name    : AvoidPlast.item3_imp_item2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:01.205351+00:00
-- url     : https://prove2.me/theorems/7fa63043-daf2-42e2-b5e9-6ec5ed5d5d57
-- title:
--   Proof of Theorem 5.14, (3)⇒(2): hardness of Diag$_\varepsilon$ implies Assumption 1.1
-- statement:
--   Item (3) of Theorem 5.14 implies Item (2): if polynomial-time machines land in $\mathrm{Diag}_\varepsilon$ on at most an $n^{-\omega(1)}$ fraction of inputs for every $\varepsilon\in(0,1)$, then Assumption 1.1 holds with $p(n)=n^{-\omega(1)}$. No derandomization hypothesis is needed.
--
--   Differences from the source:
--   - encoding: $n^{-\omega(1)}$ → an existential negligible $\nu$ (the published `QuantumPRC.Negligible`: for every real $c>0$, eventually $|\nu(n)|<n^{-c}$); reason: the standard meaning; reading R1 of the paper notes
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
--   - encoding: stretching $|x|^{\varepsilon^2}$ bits to $|x|^{\varepsilon}$ bits → lengths $\lceil n^{\varepsilon^2}\rceil$ and $\lceil n^{\varepsilon}\rceil$; reason: bit lengths are integers; matches $m_\varepsilon(n)=\lceil n^{\varepsilon^2}\rceil$ of Definition 5.13; reading R3
--   - reading: fix a universal deterministic machine $U_\varepsilon$ with budgets $n^{\varepsilon^2}$ work space and $2^{n^{\varepsilon^2}}$ steps → the function $U_\varepsilon$ denoted by it: descriptions $0^j1e$, budgets $\lceil n^{\varepsilon^2}\rceil$ bits of simulation size and $2^{\lceil n^{\varepsilon^2}\rceil}$ steps; reason: the page leaves the universal machine open; the proof uses only universality and low-space evaluability, and the bit budget is what makes both true; reading R4
--   - encoding: indexed family of circuits $C[\ell_{in}\to\ell_{out},s]$ with $s$ arbitrary → a map $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$; reason: every such map has a circuit and the size is unconstrained; reading R8
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (3)⇒(2), p.29

import Mathlib
import Definitions.Def_AvoidPlast_Assumption11
import Definitions.Def_AvoidPlast_DiagHard

namespace AvoidPlast

/-- Item (3) implies Item (2) (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (3)⇒(2), p.29). No derandomization
hypothesis is needed. -/
theorem item3_imp_item2 : DiagHard → Assumption11 := by sorry

end AvoidPlast
