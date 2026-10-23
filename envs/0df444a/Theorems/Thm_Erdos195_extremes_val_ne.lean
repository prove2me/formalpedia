-- Prove2me | Theorems.Thm_Erdos195_extremes_val_ne
-- name    : Erdos195.extremes_val_ne
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:07:21.573479+00:00
-- url     : https://prove2.me/theorems/37e8eeaf-3b86-4d8f-88af-93a84ea8081f
-- title:
--   At an $\varepsilon$-safe cut of a $4$-AP-free enumeration of $\mathbb{Z}$, nothing before the earlier extreme has the extremes' $2$-adic valuation
-- statement:
--   Let $f:\mathbb{N}\to\mathbb{Z}$ be a bijection with no monotone $4$-term arithmetic progression, and fix a cut $N$ such that the prefix $f(0),\dots,f(N-1)$ is $\varepsilon$-safe for **some** $\varepsilon:\mathbb{N}\to\{0,1\}$ (i.e. the completion "prefix, then all remaining integers in the $2$-adic order $\prec_\varepsilon$" has no monotone $4$-AP; here $x\prec_\varepsilon y$ iff the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, $k=\nu_2(y-x)$). Suppose positions $i<j<N$ carry the two extremes of the prefix (the minimum and the maximum, in either order), and let $k_0=\nu_2(f(j)-f(i))$. Then no element placed before the earlier extreme has the same valuation against it: for every $a<i$, $\nu_2(f(i)-f(a))\neq k_0$ (equivalently $f(a)\not\equiv f(j)\pmod{2^{k_0+1}}$).
--
--   Proof idea: the pairs $(a,i)$ and $(i,j)$ are both open at $N$ (their continuations $2y-x$, $3y-2x$ lie beyond the extremes, hence outside the prefix); by the digit-consistency criterion for open pairs, equal valuations $k$ would force the $k$-th digits of $f(i)$ and $f(j)$ to agree, but they differ at $k=\nu_2(f(j)-f(i))$. A necessary condition on every cut of a Ho-style chain with stage-dependent $\varepsilon$ for Erdős Problem 195; it does not decide the problem.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem extremes_val_ne (f : ℕ ≃ ℤ) (hf : ¬ HasMonotoneAP f 4) (N : ℕ)
    (hε : ∃ ε : ℕ → Bool, Safe (epsLt ε) ((List.range N).map f)) (i j : ℕ)
    (hij : i < j) (hjN : j < N)
    (hext : (∀ t < N, f i ≤ f t ∧ f t ≤ f j) ∨ (∀ t < N, f j ≤ f t ∧ f t ≤ f i))
    (a : ℕ) (hai : a < i) :
    padicValInt 2 (f i - f a) ≠ padicValInt 2 (f j - f i) := by sorry

end Erdos195
