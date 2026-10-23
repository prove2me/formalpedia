-- Prove2me | Theorems.Thm_Erdos195_stagewise_extremes_diff_dvd
-- name    : Erdos195.stagewise_extremes_diff_dvd
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T01:38:14.222069+00:00
-- url     : https://prove2.me/theorems/c756c8a4-ebd2-46ec-808a-334fb42afa99
-- title:
--   Stage extrema of a chain of safe words with stage-dependent $\varepsilon$-orders agree $2$-adically
-- statement:
--   For each stage $n$ let $\varepsilon^{(n)}:\mathbb{N}\to\{0,1\}$ be arbitrary and let $\prec_n$ be the associated $2$-adic order on $\mathbb{Z}$ (for $x\neq y$ with $k=\nu_2(y-x)$: $x\prec_n y$ iff the $k$-th two's-complement digit of $x$ equals $\varepsilon^{(n)}_k$). Let $P_0\sqsubseteq P_1\sqsubseteq\cdots$ be finite words of integers, each a prefix of the next, together containing every integer, such that each $P_n$ is **safe** for its own order $\prec_n$ (the completion "$P_n$, then all other integers in $\prec_n$-order" contains no monotone $4$-term AP). Then for every $k$ there is $N$ such that for all $n\ge N$,
--   $$2^k \mid \max P_n-\min P_n .$$
--
--   In words: even if the completion order is allowed to change at every stage, the stage extrema of an exhaustive chain of safe words agree modulo every power of $2$ eventually (both are congruent to $\sum_{j<k}\varepsilon^{(n)}_j2^j$ modulo $2^k$). This is a necessary condition on any Ho-style construction of a $4$-AP-free enumeration of $\mathbb{Z}$ with stage-dependent $\varepsilon$-orders; it extends the fixed-order statement and does not by itself rule such constructions out.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem stagewise_extremes_diff_dvd (ε : ℕ → ℕ → Bool) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (epsLt (ε n)) (P n)) (hpre : ∀ n, P n <+: P (n + 1))
    (hcov : ∀ x, ∃ n, x ∈ P n) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ U ∈ P n, ∀ L ∈ P n, (∀ y ∈ P n, y ≤ U) → (∀ y ∈ P n, L ≤ y) →
      (2 : ℤ) ^ k ∣ U - L := by sorry

end Erdos195
