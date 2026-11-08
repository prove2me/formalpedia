-- Prove2me | Theorems.Thm_AvoidPlast_family_evaluable
-- name    : AvoidPlast.family_evaluable
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:48:58.314245+00:00
-- url     : https://prove2.me/theorems/bd7dab74-65fe-449a-8b57-a78002c27bbe
-- title:
--   Proof of Theorem 5.14, (3)⇒(2): the family $C_x(d)$ is evaluable in space $O(n^{\varepsilon^2})$
-- statement:
--   For $\varepsilon\in(0,1)$, the family $C_x(d)=$ the first $\lceil n^\varepsilon\rceil$ bits of $U_\varepsilon(x,d)$, stretching $\lceil n^{\varepsilon^2}\rceil$ bits to $\lceil n^\varepsilon\rceil$ bits, is evaluable in space $O(n^{\varepsilon^2})$. This is the last sentence of Definition 5.13 applied to the family of the proof.
--
--   Differences from the source:
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
--   - encoding: stretching $|x|^{\varepsilon^2}$ bits to $|x|^{\varepsilon}$ bits → lengths $\lceil n^{\varepsilon^2}\rceil$ and $\lceil n^{\varepsilon}\rceil$; reason: bit lengths are integers; matches $m_\varepsilon(n)=\lceil n^{\varepsilon^2}\rceil$ of Definition 5.13; reading R3
--   - reading: fix a universal deterministic machine $U_\varepsilon$ with budgets $n^{\varepsilon^2}$ work space and $2^{n^{\varepsilon^2}}$ steps → the function $U_\varepsilon$ denoted by it: descriptions $0^j1e$, budgets $\lceil n^{\varepsilon^2}\rceil$ bits of simulation size and $2^{\lceil n^{\varepsilon^2}\rceil}$ steps; reason: the page leaves the universal machine open; the proof uses only universality and low-space evaluability, and the bit budget is what makes both true; reading R4
--   - encoding: indexed family of circuits $C[\ell_{in}\to\ell_{out},s]$ with $s$ arbitrary → a map $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$; reason: every such map has a circuit and the size is unconstrained; reading R8
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (3)⇒(2), p.29; Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_U

namespace AvoidPlast

/-- The family `C_x(d) =` the first `⌈n^ε⌉` bits of `U_ε(x, d)` is evaluable in space `O(n^{ε²})` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Definition 5.13 and proof of Theorem 5.14, (3)⇒(2), p.29). -/
theorem family_evaluable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    EvaluableInSpace (fun x d => (U ε x d).take (ceilPow ε x.length))
      (ceilPow (ε ^ 2)) (ceilPow ε) (fun n => (n : ℝ) ^ (ε ^ 2)) := by sorry

end AvoidPlast
