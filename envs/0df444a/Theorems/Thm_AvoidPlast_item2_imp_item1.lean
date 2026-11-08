-- Prove2me | Theorems.Thm_AvoidPlast_item2_imp_item1
-- name    : AvoidPlast.item2_imp_item1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:23.452208+00:00
-- url     : https://prove2.me/theorems/a6f4cb2b-32db-4c68-a536-1feb766438a3
-- title:
--   Proof of Theorem 5.14, (2)⇒(1): Assumption 1.1 implies low-space simulation of FP
-- statement:
--   Assume $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$. If Assumption 1.1 holds with $p(n)=n^{-\omega(1)}$, then for every $f\in\mathrm{FP}$ and every constant $\gamma>0$ there is a deterministic space-$n^\gamma$ machine computing $f$ correctly on a $1-n^{-\omega(1)}$ fraction of the $n$-bit inputs, for every sufficiently large $n$.
--
--   Differences from the source:
--   - encoding: $n^{-\omega(1)}$ → an existential negligible $\nu$ (the published `QuantumPRC.Negligible`: for every real $c>0$, eventually $|\nu(n)|<n^{-c}$); reason: the standard meaning; reading R1 of the paper notes
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
--   - encoding: stretching $|x|^{\varepsilon^2}$ bits to $|x|^{\varepsilon}$ bits → lengths $\lceil n^{\varepsilon^2}\rceil$ and $\lceil n^{\varepsilon}\rceil$; reason: bit lengths are integers; matches $m_\varepsilon(n)=\lceil n^{\varepsilon^2}\rceil$ of Definition 5.13; reading R3
--   - reading: the machine model is the RAM model (p.13), unspecified → a multitape machine with read-only input tapes, each accessed by head moves and index jumps, a fixed work alphabet and a write-only output; reason: the page does not fix a RAM; FP and space $n^\gamma$ are robust under the choice, and sublinear time needs the random access; reading R5
--   - encoding: persistent two-way read-only random tape of unstated length → a random string of the fixed length of the machine's time bound, $C(n^C+1)$, with a head that may also jump; reason: a free length function would be non-uniform advice and would make $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$ false; a jump is simulated by a walk within polynomial time and logspace
--   - encoding: indexed family of circuits $C[\ell_{in}\to\ell_{out},s]$ with $s$ arbitrary → a map $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$; reason: every such map has a circuit and the size is unconstrained; reading R8
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (2)⇒(1), p.30

import Mathlib
import Definitions.Def_AvoidPlast_PrBPstarLEqPrL
import Definitions.Def_AvoidPlast_Assumption11
import Definitions.Def_AvoidPlast_LowSpaceFP

namespace AvoidPlast

/-- Item (2) implies Item (1), under `prBP*L = prL` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (2)⇒(1), p.30). -/
theorem item2_imp_item1 (hyp : PrBPstarLEqPrL) : Assumption11 → LowSpaceFP := by sorry

end AvoidPlast
