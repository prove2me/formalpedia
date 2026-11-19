-- Prove2me | Theorems.Thm_BorelNormality_borel_conjecture
-- name    : BorelNormality.borel_conjecture
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T17:11:15.470368+00:00
-- url     : https://prove2.me/theorems/6d98d288-777d-4109-a100-c8b7dfe1b90f
-- title:
--   Borel's conjecture: irrational algebraic numbers are absolutely normal
-- statement:
--   Borel's normality conjecture (1950). Let $x$ be a real number that is **algebraic over $\mathbb{Q}$** — a root of some nonzero polynomial with rational coefficients — and **irrational**, i.e. $x \notin \mathbb{Q}$. Then $x$ is absolutely normal: it is normal in every integer base $b \ge 2$.
--
--   $$\forall x \in \mathbb{R},\quad \bigl(\mathrm{IsAlgebraic}\ \mathbb{Q}\ x \;\wedge\; \mathrm{Irrational}\ x\bigr) \;\Longrightarrow\; \forall b \ge 2,\ \mathrm{IsNormalReal}(b, x).$$
--
--   Equivalently: for every such $x$, every base $b \ge 2$ and every block of $k$ base-$b$ digits, the block occurs in the expansion of $x$ with limiting frequency $b^{-k}$ — the digits of $x$ obey the same statistical laws as independent uniformly random digits. This is the mission's goal. It is open: no irrational algebraic number has been proved normal in any base, and no counterexample is known.
--
--   **Formalization Note.** `AbsolutelyNormal` is defined in the mission file `BorelNormality_AbsolutelyNormal` as `∀ b : ℕ, 2 ≤ b → Normal.IsNormalReal b x`, building on the platform's `Normal_Core`. `IsAlgebraic ℚ x` and `Irrational x` are the Mathlib predicates.
-- source:
--   É. Borel, Sur les chiffres décimaux de √2 et divers problèmes de probabilités en chaîne, C. R. Acad. Sci. Paris 230 (1950), 591–593, MR 0034544 (conjecture that every irrational algebraic number is normal to every base); V. Becher, Normal numbers and computer science (MPRI chapter), Conjecture 3: 'Irrational algebraic numbers are absolutely normal.', https://www.irif.fr/~carton/Enseignement/MPRI/Dynam-symbol/Documents/chapter.pdf ; https://en.wikipedia.org/wiki/Normal_number, section 'Borel's normality conjecture'.

import Mathlib
import Definitions.Def_Normal_Core
import Definitions.Def_BorelNormality_AbsolutelyNormal

set_option autoImplicit false

namespace BorelNormality

theorem borel_conjecture (x : ℝ) (hx : IsAlgebraic ℚ x) (hi : Irrational x) :
    AbsolutelyNormal x := by sorry

end BorelNormality
