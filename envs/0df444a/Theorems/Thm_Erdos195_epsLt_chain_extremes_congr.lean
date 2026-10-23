-- Prove2me | Theorems.Thm_Erdos195_epsLt_chain_extremes_congr
-- name    : Erdos195.epsLt_chain_extremes_congr
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T01:06:25.603362+00:00
-- url     : https://prove2.me/theorems/071a03bd-c5b9-4b2b-acf8-525f14038e34
-- title:
--   Extrema of an exhaustive chain of $\varepsilon$-safe words converge 2-adically
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and let $\prec_\varepsilon$ be the associated $2$-adic order on $\mathbb{Z}$ (for $x\neq y$ with $k=\nu_2(y-x)$: $x\prec_\varepsilon y$ iff the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$). Let $P_0\sqsubseteq P_1\sqsubseteq\cdots$ be finite duplicate-free words, each a prefix of the next, each **safe** for $\prec_\varepsilon$ (the completion "$P_n$, then all other integers in $\prec_\varepsilon$-order" contains no monotone $4$-term AP), and together containing every integer. Put
--   $$e_k=\sum_{j<k}\varepsilon_j\,2^j .$$
--   Then for every $k$ there is $N$ such that for all $n\ge N$, both $\max P_n$ and $\min P_n$ are congruent to $e_k$ modulo $2^k$.
--
--   In words: in any exhaustive chain of $\varepsilon$-safe words, the stage maxima and minima converge $2$-adically to $\xi_\varepsilon=\sum_j\varepsilon_j2^j$. This is a necessary condition that any Ho-style construction of a 4AP-free enumeration of $\mathbb{Z}$ with a fixed completion order must satisfy (it does not by itself rule such constructions out, since the extrema can still tend to $\pm\infty$).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (idea suggested via GPT, Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_chain_extremes_congr (ε : ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt ε) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ M ∈ P n, ((∀ y ∈ P n, y ≤ M) ∨ (∀ y ∈ P n, M ≤ y)) →
      (2 : ℤ) ^ k ∣ M - ∑ j ∈ Finset.range k, (if ε j then (2 : ℤ) ^ j else 0) := by sorry

end Erdos195
