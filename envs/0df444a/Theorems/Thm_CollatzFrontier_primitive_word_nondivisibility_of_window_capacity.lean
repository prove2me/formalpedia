-- Prove2me | Theorems.Thm_CollatzFrontier_primitive_word_nondivisibility_of_window_capacity
-- name    : CollatzFrontier.primitive_word_nondivisibility_of_window_capacity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:58:54.662934+00:00
-- url     : https://prove2.me/theorems/f75812bb-4e48-47ef-92b4-c49d47deb758
-- title:
--   A window-complexity obstruction to primitive-word Syracuse realizability
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$ be the Syracuse (accelerated Collatz) map. Let $w=(a_0,\dots,a_{p-1})$ be a finite list of natural numbers with $p=\operatorname{length}(w)\ge1$ and $K=w.\mathrm{sum}=\sum_i a_i$, and call $w$ *primitive* if no proper nontrivial left cyclic rotation of $w$ equals $w$: $\operatorname{rotate}_d(w)\ne w$ for every $0<d<p$.
--
--   Write $C(w)$ for the canonical affine constant already available on the platform (`Definitions.Def_syracuseOffsetMod`), defined by $C([])=0$ and $C(a::b)=3^{\operatorname{length}(b)}+2^aC(b)$, and put $D=2^K-3^p$.
--
--   For $k\ge0$, let $N_k(w)$ (`Definitions.Def_collatzFrontierWordWindows`, `wordWindowCount`) be the number of distinct length-$k$ cyclic windows of $w$: the number of distinct values taken by the block of $k$ consecutive entries of $w$ starting at index $i$ (indices wrap around via rotation) as $i$ ranges over $\{0,\dots,p-1\}$.
--
--   Assume:
--
--   1. $w$ is nonempty and every entry of $w$ is strictly positive;
--   2. $w$ is primitive;
--   3. the power gap $3^p<2^K$ (equivalently $D>0$);
--   4. every rotated affine constant lies in an explicit interval given as a multiple of $D$: for all $d<p$,
--   $$L\cdot D \;\le\; C(w.\mathrm{rotate}(d)) \;\le\; U\cdot D;$$
--   5. the window-capacity failure
--   $$N_k(w)\cdot\Bigl(\Bigl\lfloor\tfrac{U-L}{2\cdot3^k}\Bigr\rfloor+1\Bigr) \;<\; p.$$
--
--   Then
--   $$D \nmid C(w),$$
--   i.e. the exact Syracuse-recurrence quotient $C(w)/D$ is not a natural number, so $w$ cannot be the valuation word of **any** Syracuse-periodic orbit: there is no $m>0$ with $T^p(m)=m$ whose dyadic-valuation sequence equals $w$.
--
--   This is a sufficient obstruction: whenever a range $[L\cdot D,\,U\cdot D]$ for every rotated affine constant and a small window count $N_k(w)$ are both established for a candidate word, nondivisibility -- and hence nonrealizability of $w$ as a cycle word -- follows immediately.
--
--   This theorem does not, by itself, lower the mission's established minimum period bound of $6291$ for a nontrivial Syracuse cycle, nor does it resolve the remaining unbounded primitive-word tail. It supplies one additional, generically applicable filter that any surviving candidate word must still pass, complementing the open word-level frontier at [this platform theorem](https://prove2.me/theorems/9f28e7b8-804f-4efd-83e3-1e68362b2b34), whose rotated-baseline hypothesis supplies the lower end $L$; an upper bound $U$ must be established separately.
--
--   **Formalization Note.** The hypothesis `hbounds` is an input about the specific candidate word under consideration, not an unconditional claim about all Syracuse cycles; divisibility of $D$ into $C(w)$ is never assumed, and no cycle is presupposed to exist anywhere in the statement.
-- source:
--   Original result of this contribution. Private repository collatz-frontier, branch research/window-complexity-20261002, commit a3a13a7cb543ccbc29d83fe91aaa68f59fa13874, file lean/CollatzFrontier/WindowComplexity.lean, declaration CollatzFrontier.primitive_word_nondivisibility_of_window_capacity (with closure WordRealization.lean, DistinctCycleBudget.lean, UniformDescent.lean), doc docs/window-complexity.md. Builds on the platform's canonical affine constant Definitions.Def_syracuseOffsetMod (credits https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7) and complements the open primitive-word frontier https://prove2.me/theorems/9f28e7b8-804f-4efd-83e3-1e68362b2b34, whose rotated-baseline range hypothesis supplies the lower end L of the range this theorem consumes (an upper bound U must be established separately); it is not a proof of that theorem.

import Mathlib
import Definitions.Def_syracuseOffsetMod
import Definitions.Def_collatzFrontierWordWindows

namespace CollatzFrontier

theorem primitive_word_nondivisibility_of_window_capacity (w : List ℕ) (k L U : ℕ)
    (hw : w ≠ []) (hpositive : ∀ a ∈ w, 0 < a)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hbounds : ∀ d : ℕ, d < w.length →
      L * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d) ∧
      syracuseAffineConstant (w.rotate d) ≤ U * (2 ^ w.sum - 3 ^ w.length))
    (hcapacity : wordWindowCount w k * ((U - L) / (2 * 3 ^ k) + 1) < w.length) :
    ¬ (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry

end CollatzFrontier
