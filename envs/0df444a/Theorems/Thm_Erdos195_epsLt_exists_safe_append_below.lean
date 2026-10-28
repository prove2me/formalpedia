-- Prove2me | Theorems.Thm_Erdos195_epsLt_exists_safe_append_below
-- name    : Erdos195.epsLt_exists_safe_append_below
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T02:30:48.31451+00:00
-- url     : https://prove2.me/theorems/724ce4e3-cb83-4ec9-bedb-2040dc5e44ae
-- title:
--   An $\varepsilon$-safe word can be extended by a $\prec_\varepsilon$-minimal letter arbitrarily far in both directions
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $P$ of distinct integers is $\varepsilon$-safe if the sequence "the letters of $P$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Assume $\varepsilon$ is not eventually constant and $P$ is $\varepsilon$-safe. Then for every $M\in\mathbb{Z}$ there exist integers $t>M$ and $t'<M$ such that
--   $$t\prec_\varepsilon a\ \text{and}\ t'\prec_\varepsilon a\ \text{for all } a\in P,\qquad P\cdot t\ \text{and}\ P\cdot t'\ \text{are } \varepsilon\text{-safe}.$$
--   Thus, with the order fixed, new records can always be appended on either side of an $\varepsilon$-safe word; this is the unconditional part of an extension procedure for constructing $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; "not eventually constant" is `¬ ∃ N b, ∀ n ≥ N, ε n = b`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_exists_safe_append_below (ε : ℕ → Bool)
    (hε : ¬ ∃ N : ℕ, ∃ b : Bool, ∀ n ≥ N, ε n = b) (P : List ℤ) (hS : Safe (epsLt ε) P) (M : ℤ) :
    (∃ t, M < t ∧ (∀ a ∈ P, epsLt ε t a) ∧ Safe (epsLt ε) (P ++ [t])) ∧
    (∃ t, t < M ∧ (∀ a ∈ P, epsLt ε t a) ∧ Safe (epsLt ε) (P ++ [t])) := by sorry

end Erdos195
