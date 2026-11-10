-- Prove2me | Theorems.Thm_FatFlat_Hereditary_observation_2
-- name    : FatFlat.Hereditary.observation_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:24.459199+00:00
-- url     : https://prove2.me/theorems/44955da9-045d-448d-b64a-ff37906e5fad
-- title:
--   Observation 2 — $K(r,n)$ and $W(r,n)$ contain every $n$-vertex graph as a $(\lfloor r/4\rfloor+10)$-shallow $(\lfloor r/2\rfloor-10)$-fat minor
-- statement:
--   Let $r\ge3$ and $n\in\mathbb N$. For every graph $H$ on $n$ vertices, both the $r$-subdivided clique $K(r,n)$ and the $r$-web $W(r,n)$ contain $H$ as a $(\lfloor r/4\rfloor+10)$-shallow $(\lfloor r/2\rfloor-10)$-fat minor.
--
--   For $r<22$ the printed fatness $\lfloor r/2\rfloor-10$ is $\le 0$; Lean uses the truncated natural-number value $\max(\lfloor r/2\rfloor-10,0)$, and a 0-fat condition imposes no distance requirement.
--
--   Differences from the source:
--   - encoding: every n-vertex graph → every H : SimpleGraph (Fin n); reason: fat-minor containment is invariant under isomorphism
--   - encoding: fatness ⌊r/2⌋ − 10 (≤ 0 when r < 22, where the paper's δ > 0 is undefined) → r / 2 - 10 in ℕ (truncated to 0); reason: for r ≥ 22 identical; for r < 22 the printed fatness is nonpositive and the 0-fat condition, like any nonpositive one, is vacuous
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Observation 2, p. 21 (PDF p. 23). Verbatim: 'Observation 2. K(r, n) and W(r, n) both contain every n-vertex graph as a (⌊r/4⌋ + 10)-shallow (⌊r/2⌋ − 10)-fat minor.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Observation 2** (arXiv:2607.21474, p. 21). `K(r, n)` and `W(r, n)` both contain every
`n`-vertex graph as a `(⌊r/4⌋ + 10)`-shallow `(⌊r/2⌋ − 10)`-fat minor (`r ≥ 3`, as in
Definition 3.4; the fatness is the truncated `r / 2 - 10 : ℕ`). -/
theorem observation_2 (r n : ℕ) (hr : 3 ≤ r) (H : SimpleGraph (Fin n)) :
    IsShallowFatMinor H (subdividedClique r n) (r / 4 + 10) (r / 2 - 10) ∧
    IsShallowFatMinor H (web r n) (r / 4 + 10) (r / 2 - 10) := by sorry

end FatFlat.Hereditary
