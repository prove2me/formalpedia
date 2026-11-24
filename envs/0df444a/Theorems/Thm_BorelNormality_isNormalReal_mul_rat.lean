-- Prove2me | Theorems.Thm_BorelNormality_isNormalReal_mul_rat
-- name    : BorelNormality.isNormalReal_mul_rat
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T17:09:39.698916+00:00
-- url     : https://prove2.me/theorems/a87ba652-e3a9-4aff-a73b-d5206c167528
-- title:
--   Wall: nonzero rational multiples preserve normality
-- statement:
--   Wall's invariance theorem (1949). Let $b \ge 2$ be an integer and $x$ a real number normal in base $b$. If $a$ is a nonzero rational number, then $x \cdot a$ is again normal in base $b$:
--
--   $$\mathrm{IsNormalReal}(b, x) \;\wedge\; a \in \mathbb{Q}\setminus\{0\} \;\Longrightarrow\; \mathrm{IsNormalReal}(b, x a).$$
--
--   Normality in a fixed base is thus invariant under nonzero rational scaling (and, applying the theorem to $1/a$, the converse holds as well). This lets reductions renormalise a number — for instance scale it into $(0,1)$ — without losing normality, and is a basic structural lemma of the theory.
--
--   **Formalization Note.** The base $b$ and the number $x$ are implicit binders; $a$ is coerced from $\mathbb{Q}$ to $\mathbb{R}$. The predicate is `Normal.IsNormalReal` from `Normal_Core`.
-- source:
--   D. D. Wall, Normal Numbers, Ph.D. thesis, University of California, Berkeley, 1949. As stated in https://en.wikipedia.org/wiki/Normal_number, section 'Properties': 'If x is normal in base b, and a ≠ 0 is a rational number, then x·a is also normal in base b.'

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

namespace BorelNormality

theorem isNormalReal_mul_rat {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : Normal.IsNormalReal b x) (a : ℚ) (ha : a ≠ 0) :
    Normal.IsNormalReal b (x * (a : ℝ)) := by sorry

end BorelNormality
