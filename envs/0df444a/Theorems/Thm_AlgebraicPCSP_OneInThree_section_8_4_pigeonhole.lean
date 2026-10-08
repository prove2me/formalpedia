-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_section_8_4_pigeonhole
-- name    : AlgebraicPCSP.OneInThree.section_8_4_pigeonhole
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:24.530608+00:00
-- url     : https://prove2.me/theorems/8d349fd2-8114-4f37-987d-56049a61fcd6
-- title:
--   §8.4 — choice of l₁ < l₂ in (p/3 − 2|D|, p/3) with s(1^{l₁}0…) = s(1^{l₂}0…)
-- statement:
--   Let $D$ be a finite set, $f:\{0,1\}\to D$ any map, $p$ a prime with $p>60|D|$, and $s:D^p\to D$ any operation. Then there are natural numbers $l_1,l_2$ with
--   $$\frac p3-2|D|<l_1<l_2<\frac p3\qquad\text{and}\qquad s(\underbrace{1,\dots,1}_{l_1},0,\dots,0)=s(\underbrace{1,\dots,1}_{l_2},0,\dots,0),$$
--   where $0,1$ are evaluated in $D$ through $f$.
--
--   This is the pigeonhole step that opens §8.4: the interval contains $2|D|>|D|$ integers, so two of the $p$-tuples receive the same value of $s$. The two matrices built from $l_1$ and $l_2$ then have equal $t$-values but areas on opposite sides of $1/3$.
--
--   **Formalization Note** The inequalities are in $\mathbb Q$. No property of $s$ is needed. The paper prints "$2|D|>D$ integers", meaning $2|D|>|D|$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, pp. 57–58, §8.4 (unnumbered: choice of l₁ and l₂)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

/-- §8.4 (pp. 57–58), the choice of `l₁, l₂`: for any `p`-ary operation `s` on a finite set
`D`, any `f : {0, 1} → D`, and a prime `p > 60|D|`, there are natural numbers `l₁, l₂` with
`p/3 − 2|D| < l₁ < l₂ < p/3` and `s(f ∘ (1^{l₁} 0^{p−l₁})) = s(f ∘ (1^{l₂} 0^{p−l₂}))`. -/
theorem section_8_4_pigeonhole {D : Type} [Fintype D] [DecidableEq D] (f : Fin 2 → D)
    {p : ℕ} (hp : p.Prime) (hpD : 60 * Fintype.card D < p) (s : (Fin p → D) → D) :
    ∃ l₁ l₂ : ℕ, (p : ℚ) / 3 - 2 * (Fintype.card D : ℚ) < l₁ ∧ l₁ < l₂ ∧
      (l₂ : ℚ) < (p : ℚ) / 3 ∧
      s (fun j => f (prefixOnes p l₁ j)) = s (fun j => f (prefixOnes p l₂ j)) := by sorry

end AlgebraicPCSP.OneInThree
