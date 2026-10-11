-- Prove2me | Theorems.Thm_CLRS_Chapter4Master_master_theorem
-- name    : CLRS.Chapter4Master.master_theorem
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:07:41.4948+00:00
-- url     : https://prove2.me/theorems/7f9820cc-f5da-4745-9f6d-e0d59496a9a0
-- title:
--   CLRS Chapter 4, §4.5: the three master-theorem cases with rounded natural sizes
-- statement:
--   A recurrence package consists of real-valued costs $T,f$,
--   a positive real multiplier $a$, a natural child function $r$, and a positive
--   cutoff $b_0$. It requires positive base costs for every $n<b_0$, nonnegative
--   toll at every size, strictly smaller children above the cutoff, and
--   $T(n)=aT(r(n))+f(n)$ there.
--
--   Bounded-error rounding means a real divisor $b>1$ and a
--   uniform real bound on $|r(n)-n/b|$ for every natural size. All asymptotic
--   comparisons are eventual as natural $n$ tends to infinity.
--
--   Assume additionally $a\ge1$ and put $p=\log_b a$. The following three
--   implications hold for this same recurrence:
--
--   1. For every real $\varepsilon>0$, if $f(n)=O(n^{p-\varepsilon})$, then
--      $T(n)=\Theta(n^p)$.
--   2. For every real $q\ge0$, if $f(n)=\Theta(n^p(\log n)^q)$, then
--      $T(n)=\Theta(n^p(\log n)^{q+1})$.
--   3. For every real $\varepsilon>0$ and $c<1$, if
--      $n^{p+\varepsilon}=O(f(n))$ and eventually $af(r(n))\le cf(n)$,
--      then $T(n)=\Theta(f(n))$.
--
--   $$\text{smaller toll: }\Theta(n^p),\qquad
--   \text{critical toll: }\Theta(n^p(\log n)^{q+1}),\qquad
--   \text{dominant regular toll: }\Theta(f(n)).$$
--
--   The logarithm is natural except in $\log_b a$. Floor and ceiling division
--   are available instances of bounded-error rounding; recursive decrease
--   remains a separate premise in the recurrence package. In case three,
--   regularity is checked at the actual rounded child, not an unrounded real
--   argument. Cases one and two do not require monotonicity or smoothness of
--   the original toll. Positive base costs include size zero, so a numerical
--   recurrence with $T(0)=0$ does not directly fit this package.
--
--   This is a reusable theorem about numerical cost functions. Applying it to
--   a program additionally requires proof that a terminating execution has
--   the stated recurrence. It formalizes the selected §4.5 discrete result;
--   it does not claim coverage of §§4.6–4.7.
--
--   **Platform namespace.** The imported Chapter 4 source declarations live under `CLRS` in this upload to avoid collisions with independently published compiler versions. The immutable source reference retains the original declaration names.
-- source:
--   Algo2Lean Chapter 4 development, declaration Chapter4Master.master_theorem, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/MasterTheorem.lean#L29-L44

import Definitions.Def_CLRS_Chapter4_Master_Basic
import Definitions.Def_CLRS_Chapter4_Master_CaseTwo
import Definitions.Def_CLRS_Chapter4_Master_Rounding
import Definitions.Def_CLRS_Chapter4_Substitution
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.AkraBazzi.AkraBazzi
import Mathlib.Tactic
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS
end CLRS
open CLRS
namespace CLRS.Chapter4Master
end CLRS.Chapter4Master
open CLRS.Chapter4Master
open Filter Asymptotics Real

theorem CLRS.Chapter4Master.master_theorem {T f : ℕ → ℝ} {a b : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) (hr : RoundedDivision b r) (ha : 1 ≤ a) :
    (∀ ε : ℝ, 0 < ε →
      f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (logb b a - ε)) →
      T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a)) ∧
    (∀ k : ℝ, 0 ≤ k →
      f =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a * (log n) ^ k) →
      T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a * (log n) ^ (k + 1))) ∧
    (∀ ε c : ℝ, 0 < ε → c < 1 →
      (fun n : ℕ => (n : ℝ) ^ (logb b a + ε)) =O[atTop] f →
      (∀ᶠ n in atTop, a * f (r n) ≤ c * f n) → T =Θ[atTop] f) := by sorry
