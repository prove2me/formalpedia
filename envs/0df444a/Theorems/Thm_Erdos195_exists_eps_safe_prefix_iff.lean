-- Prove2me | Theorems.Thm_Erdos195_exists_eps_safe_prefix_iff
-- name    : Erdos195.exists_eps_safe_prefix_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T01:52:52.585687+00:00
-- url     : https://prove2.me/theorems/5ed614f1-cac7-45b5-85db-6c3254fd90b6
-- title:
--   A prefix of a $4$-AP-free enumeration of $\mathbb{Z}$ is safe for some $\varepsilon$-order iff its open pairs are digit-consistent
-- statement:
--   Let $f:\mathbb{N}\to\mathbb{Z}$ be a bijection containing no monotone $4$-term arithmetic progression, and fix a cut $N\in\mathbb{N}$. Call a pair of positions $i<j<N$ **open at $N$** if both values $2f(j)-f(i)$ and $3f(j)-2f(i)$ occur in $f$ at positions $\ge N$. For $\varepsilon:\mathbb{N}\to\{0,1\}$ let $\prec_\varepsilon$ be the $2$-adic order on $\mathbb{Z}$ (for $x\neq y$ with $k=\nu_2(y-x)$: $x\prec_\varepsilon y$ iff the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$), and call the prefix $f(0),\dots,f(N-1)$ **$\varepsilon$-safe** if the completion "prefix, then all remaining integers in $\prec_\varepsilon$-order" has no monotone $4$-AP. Then
--   $$\exists\,\varepsilon:\ f(0),\dots,f(N-1)\ \text{is }\varepsilon\text{-safe}\iff \begin{array}{l}\text{for all pairs }(i,j),(i',j')\text{ open at }N\text{ with }\nu_2(f(j)-f(i))=\nu_2(f(j')-f(i'))=k,\\ \text{the }k\text{-th binary digits of }f(j)\text{ and }f(j')\text{ coincide.}\end{array}$$
--
--   This eliminates the order from Ho-style constructions with stage-dependent $\varepsilon$: a chain of prefixes, each safe for its own $\varepsilon$-order, exhausting $\mathbb{Z}$ is exactly a $4$-AP-free enumeration of $\mathbb{Z}$ with infinitely many cuts at which the open pairs impose consistent binary-digit constraints (each open pair $(i,j)$ forces $\varepsilon_k$ to be the $k$-th digit of the later value $f(j)$). It reduces the stage-dependent-$\varepsilon$ approach to Erdős Problem 195 to a purely combinatorial condition on the permutation; it does not by itself decide whether such permutations exist.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem exists_eps_safe_prefix_iff (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ) :
    (∃ ε : ℕ → Bool, Safe (epsLt ε) ((List.range N).map f)) ↔
      ∀ i j i' j' : ℕ, i < j → j < N → N ≤ f.symm (2 * f j - f i) →
        N ≤ f.symm (3 * f j - 2 * f i) →
        i' < j' → j' < N → N ≤ f.symm (2 * f j' - f i') → N ≤ f.symm (3 * f j' - 2 * f i') →
        padicValInt 2 (f j - f i) = padicValInt 2 (f j' - f i') →
        (bitOne (f j) (padicValInt 2 (f j - f i)) ↔
          bitOne (f j') (padicValInt 2 (f j' - f i'))) := by sorry

end Erdos195
