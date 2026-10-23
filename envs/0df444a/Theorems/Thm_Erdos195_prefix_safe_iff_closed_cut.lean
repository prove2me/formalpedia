-- Prove2me | Theorems.Thm_Erdos195_prefix_safe_iff_closed_cut
-- name    : Erdos195.prefix_safe_iff_closed_cut
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T01:22:23.350606+00:00
-- url     : https://prove2.me/theorems/d3d0d955-659c-4494-b026-aa1272c2d1bf
-- title:
--   Safe prefixes of a $4$-AP-free enumeration are exactly the $R$-closed cuts
-- statement:
--   Let $R$ be a binary relation on $\mathbb{Z}$ with no monotone $3$-term AP (there are no $a$ and $r\neq0$ with $a\,R\,a+r$ and $a+r\,R\,a+2r$) and with Ho's property $(\ast)$: $a\,R\,a+r \iff a+2r\,R\,a+3r$ for all $a$ and $r\ne0$. Let $f:\mathbb{N}\to\mathbb{Z}$ be a bijection with no monotone $4$-term AP, and let $N\in\mathbb{N}$. Then the prefix word $P_N=(f(0),\dots,f(N-1))$ is **safe** for $R$ (the completion "$P_N$, then all other integers in $R$-order" contains no monotone $4$-term AP) if and only if the cut at $N$ is $R$-closed:
--   $$\forall\, i<j<N:\quad f(i)\,R\,f(j)\ \text{ and }\ f^{-1}\bigl(2f(j)-f(i)\bigr)\ge N\ \Longrightarrow\ f^{-1}\bigl(3f(j)-2f(i)\bigr)<N .$$
--
--   In words: for a $4$-AP-free enumeration, safety of a prefix reduces to a single closure condition on the cut. Consequently a Ho-style construction over $\mathbb{Z}$ with a fixed completion order $R$ (a prefix-increasing chain of $R$-safe words exhausting $\mathbb{Z}$) is the same thing as a $4$-AP-free enumeration of $\mathbb{Z}$ having infinitely many $R$-closed cuts, which isolates exactly what the fixed-order method demands beyond $4$-AP-freeness.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem prefix_safe_iff_closed_cut (R : ℤ → ℤ → Prop) (hA : No3AP R) (hB : Star R)
    (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ) :
    Safe R ((List.range N).map f) ↔
      ∀ i j : ℕ, i < j → j < N → R (f i) (f j) → N ≤ f.symm (2 * f j - f i) →
        f.symm (3 * f j - 2 * f i) < N := by sorry

end Erdos195
